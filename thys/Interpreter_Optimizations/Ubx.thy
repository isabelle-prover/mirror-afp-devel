theory Ubx
  imports Global OpUbx Env
    "VeriComp.Language"
begin


section \<open>Unboxed caching\<close>

subsection \<open>Static representation\<close>

datatype ('dyn, 'var, 'fun, 'label, 'op, 'opinl, 'opubx, 'num, 'bool) instr =
  IPush 'dyn | IPushUbx1 'num | IPushUbx2 'bool |
  IPop |
  IGet nat | IGetUbx type nat |
  ISet nat | ISetUbx type nat |
  ILoad 'var | ILoadUbx type 'var |
  IStore 'var | IStoreUbx type 'var |
  IOp 'op | IOpInl 'opinl | IOpUbx 'opubx |
  is_jump: ICJump 'label 'label |
  is_fun_call: ICall 'fun |
  is_return: IReturn

locale ubx =
  Fenv: env F_empty F_get F_add F_to_list +
  Henv: env heap_empty heap_get heap_add heap_to_list +
  nary_operations_ubx
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy>
    \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll>
    uninitialized is_true is_false box_ubx1 unbox_ubx1 box_ubx2 unbox_ubx2
    \<UU>\<bb>\<xx>\<OO>\<pp> \<UU>\<bb>\<xx> \<BB>\<oo>\<xx> \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
  for
    \<comment> \<open>Functions environment\<close>
    F_empty and
    F_get :: "'fenv \<Rightarrow> 'fun \<Rightarrow> ('label, ('dyn, 'var, 'fun, 'label, 'op, 'opinl, 'opubx, 'num, 'bool) instr) fundef option" and
    F_add and F_to_list and

    \<comment> \<open>Memory heap\<close>
    heap_empty and
    heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and
    heap_add and heap_to_list and

    \<comment> \<open>Dynamic values\<close>
    uninitialized :: 'dyn and is_true and is_false and

    \<comment> \<open>Unboxed values\<close>
    box_ubx1 and unbox_ubx1 and
    box_ubx2 and unbox_ubx2 and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy> and
    \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op" and
    \<UU>\<bb>\<xx>\<OO>\<pp> :: "'opubx \<Rightarrow> ('dyn, 'num, 'bool) unboxed list \<Rightarrow> ('dyn, 'num, 'bool) unboxed option" and
    \<UU>\<bb>\<xx> :: "'opinl \<Rightarrow> type option list \<Rightarrow> 'opubx option" and
    \<BB>\<oo>\<xx> :: "'opubx \<Rightarrow> 'opinl" and
    \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
begin


lemmas map_option_funtype_comp_map_entry_rewrite_fundef_body[simp] =
  Fenv.map_option_comp_map_entry[of _ funtype "\<lambda>fd. rewrite_fundef_body fd l pc instr" for l pc instr, simplified]

fun generalize_instr where
  "generalize_instr (IPushUbx1 n) = IPush (box_ubx1 n)" |
  "generalize_instr (IPushUbx2 b) = IPush (box_ubx2 b)" |
  "generalize_instr (IGetUbx _ n) = IGet n" |
  "generalize_instr (ISetUbx _ n) = ISet n" |
  "generalize_instr (ILoadUbx _ x) = ILoad x" |
  "generalize_instr (IStoreUbx _ x) = IStore x" |
  "generalize_instr (IOpUbx opubx) = IOpInl (\<BB>\<oo>\<xx> opubx)" |
  "generalize_instr instr = instr"

lemma instr_sel_generalize_instr[simp]:
  "is_jump (generalize_instr instr) \<longleftrightarrow> is_jump instr"
  "is_fun_call (generalize_instr instr) \<longleftrightarrow> is_fun_call instr"
  "is_return (generalize_instr instr) \<longleftrightarrow> is_return instr"
  unfolding atomize_conj
  by (cases instr; simp)

lemma instr_sel_generalize_instr_comp[simp]:
  "is_jump \<circ> generalize_instr = is_jump" and
  "is_fun_call \<circ> generalize_instr = is_fun_call" and
  "is_return \<circ> generalize_instr = is_return"
  unfolding atomize_conj
  using instr_sel_generalize_instr by auto

fun generalize_fundef where
  "generalize_fundef (Fundef xs ar ret locals) =
    Fundef (map_ran (\<lambda>_. map generalize_instr) xs) ar ret locals"

lemma generalize_instr_idempotent[simp]:
  "generalize_instr (generalize_instr x) = generalize_instr x"
  by (cases x) simp_all

lemma generalize_instr_idempotent_comp[simp]:
  "generalize_instr \<circ> generalize_instr = generalize_instr"
  by fastforce

lemma length_body_generalize_fundef[simp]: "length (body (generalize_fundef fd)) = length (body fd)"
  by (cases fd) (simp add: map_ran_def)

lemma arity_generalize_fundef[simp]: "arity (generalize_fundef fd) = arity fd"
  by (cases fd) simp

lemma return_generalize_fundef[simp]: "return (generalize_fundef fd) = return fd"
  by (cases fd) simp

lemma fundef_locals_generalize[simp]: "fundef_locals (generalize_fundef fd) = fundef_locals fd"
  by (cases fd; simp)

lemma funtype_generalize_fundef[simp]: "funtype (generalize_fundef fd) = funtype fd"
  by (cases fd; simp add: funtype_def)

lemmas map_option_comp_map_entry_generalize_fundef[simp] =
  Fenv.map_option_comp_map_entry[of _ funtype generalize_fundef, simplified]

lemma image_fst_set_body_generalize_fundef[simp]:
  "fst ` set (body (generalize_fundef fd)) = fst ` set (body fd)"
  by (cases fd) (simp add: dom_map_ran)

lemma map_of_generalize_fundef_conv:
  "map_of (body (generalize_fundef fd)) l = map_option (map generalize_instr) (map_of (body fd) l)"
  by (cases fd) (simp add: map_ran_conv)

lemma map_option_arity_get_map_entry_generalize_fundef[simp]:
  "map_option arity \<circ> F_get (Fenv.map_entry F2 f generalize_fundef) =
   map_option arity \<circ> F_get F2"
  by (auto intro: Fenv.map_option_comp_map_entry)

lemma instr_at_generalize_fundef_conv:
  "instr_at (generalize_fundef fd) l = map_option generalize_instr o instr_at fd l"
proof (intro ext)
  fix n
  show "instr_at (generalize_fundef fd) l n = (map_option generalize_instr \<circ> instr_at fd l) n"
  proof (cases fd)
    case (Fundef bblocks ar locals)
    then show ?thesis
      by (cases "map_of bblocks l") (simp_all add: instr_at_def map_ran_conv)
  qed
qed


subsection \<open>Semantics\<close>

inductive step (infix "\<rightarrow>" 55) where
  step_push:
    "next_instr (F_get F) f l pc = Some (IPush d) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpDyn d # \<Sigma>) # st)" |

  step_push_ubx1:
    "next_instr (F_get F) f l pc = Some (IPushUbx1 n) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpUbx1 n # \<Sigma>) # st)" |

  step_push_ubx2:
    "next_instr (F_get F) f l pc = Some (IPushUbx2 b) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpUbx2 b # \<Sigma>) # st)" |

  step_pop:
    "next_instr (F_get F) f l pc = Some IPop \<Longrightarrow>
    State F H (Frame f l pc R (x # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R \<Sigma> # st)" |

  step_get:
    "next_instr (F_get F) f l pc = Some (IGet n) \<Longrightarrow>
    n < length R \<Longrightarrow> cast_Dyn (R ! n) = Some d \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpDyn d # \<Sigma>) # st)" |

  step_get_ubx_hit:
    "next_instr (F_get F) f l pc = Some (IGetUbx \<tau> n) \<Longrightarrow>
    n < length R \<Longrightarrow> cast_Dyn (R ! n) = Some d \<Longrightarrow> unbox \<tau> d = Some blob \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (blob # \<Sigma>) # st)" |

  step_get_ubx_miss:
    "next_instr (F_get F) f l pc = Some (IGetUbx \<tau> n) \<Longrightarrow>
    n < length R \<Longrightarrow> cast_Dyn (R ! n) = Some d \<Longrightarrow> unbox \<tau> d = None \<Longrightarrow>
    F' = Fenv.map_entry F f generalize_fundef \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F' H (box_stack f (Frame f l (Suc pc) R (OpDyn d # \<Sigma>) # st))" |

  step_set:
    "next_instr (F_get F) f l pc = Some (ISet n) \<Longrightarrow>
    n < length R \<Longrightarrow> cast_Dyn blob = Some d \<Longrightarrow> R' = R[n := OpDyn d] \<Longrightarrow>
    State F H (Frame f l pc R (blob # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R' \<Sigma> # st)" |

  step_set_ubx:
    "next_instr (F_get F) f l pc = Some (ISetUbx \<tau> n) \<Longrightarrow>
    n < length R \<Longrightarrow> cast_and_box \<tau> blob = Some d \<Longrightarrow> R' = R[n := OpDyn d] \<Longrightarrow>
    State F H (Frame f l pc R (blob # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R' \<Sigma> # st)" |

  step_load:
    "next_instr (F_get F) f l pc = Some (ILoad x) \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> heap_get H (x, i') = Some d \<Longrightarrow>
    State F H (Frame f l pc R (i # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpDyn d # \<Sigma>) # st)" |

  step_load_ubx_hit:
    "next_instr (F_get F) f l pc = Some (ILoadUbx \<tau> x) \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> heap_get H (x, i') = Some d \<Longrightarrow> unbox \<tau> d = Some blob \<Longrightarrow>
    State F H (Frame f l pc R (i # \<Sigma>) # st) \<rightarrow> State F H (Frame f l (Suc pc) R (blob # \<Sigma>) # st)" |

  step_load_ubx_miss:
    "next_instr (F_get F) f l pc = Some (ILoadUbx \<tau> x) \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> heap_get H (x, i') = Some d \<Longrightarrow> unbox \<tau> d = None \<Longrightarrow>
    F' = Fenv.map_entry F f generalize_fundef \<Longrightarrow>
    State F H (Frame f l pc R (i # \<Sigma>) # st) \<rightarrow> State F' H (box_stack f (Frame f l (Suc pc) R (OpDyn d # \<Sigma>) # st))"  |

  step_store:
    "next_instr (F_get F) f l pc = Some (IStore x) \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> cast_Dyn y = Some d \<Longrightarrow> heap_add H (x, i') d = H' \<Longrightarrow>
    State F H (Frame f l pc R (i # y # \<Sigma>) # st) \<rightarrow> State F H' (Frame f l (Suc pc) R \<Sigma> # st)" |

  step_store_ubx:
    "next_instr (F_get F) f l pc = Some (IStoreUbx \<tau> x) \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> cast_and_box \<tau> blob = Some d \<Longrightarrow> heap_add H (x, i') d = H' \<Longrightarrow>
    State F H (Frame f l pc R (i # blob # \<Sigma>) # st) \<rightarrow> State F H' (Frame f l (Suc pc) R \<Sigma> # st)" |

  step_op:
    "next_instr (F_get F) f l pc = Some (IOp op) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    ap_map_list cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<II>\<nn>\<ll> op \<Sigma>' = None \<Longrightarrow> \<OO>\<pp> op \<Sigma>' = x \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_inl:
    "next_instr (F_get F) f l pc = Some (IOp op) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    ap_map_list cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<II>\<nn>\<ll> op \<Sigma>' = Some opinl \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl \<Sigma>' = x \<Longrightarrow>
    F' = Fenv.map_entry F f (\<lambda>fd. rewrite_fundef_body fd l pc (IOpInl opinl)) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F' H (Frame f l (Suc pc) R (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_inl_hit:
    "next_instr (F_get F) f l pc = Some (IOpInl opinl) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    ap_map_list cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<II>\<ss>\<II>\<nn>\<ll> opinl \<Sigma>' \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl \<Sigma>' = x \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_inl_miss:
    "next_instr (F_get F) f l pc = Some (IOpInl opinl) \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    ap_map_list cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<not> \<II>\<ss>\<II>\<nn>\<ll> opinl \<Sigma>' \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl \<Sigma>' = x \<Longrightarrow>
    F' = Fenv.map_entry F f (\<lambda>fd. rewrite_fundef_body fd l pc (IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))) \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F' H (Frame f l (Suc pc) R (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_ubx:
    "next_instr (F_get F) f l pc = Some (IOpUbx opubx) \<Longrightarrow>
    \<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx) = op \<Longrightarrow> \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    \<UU>\<bb>\<xx>\<OO>\<pp> opubx (take ar \<Sigma>) = Some x \<Longrightarrow>
    State F H (Frame f l pc R \<Sigma> # st) \<rightarrow> State F H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st)" |

  step_cjump:
    "next_instr (F_get F) f l pc = Some (ICJump l\<^sub>t l\<^sub>f) \<Longrightarrow>
    cast_Dyn y = Some d \<Longrightarrow> is_true d \<and> l' = l\<^sub>t \<or> is_false d \<and> l' = l\<^sub>f \<Longrightarrow>
    State F H (Frame f l pc R (y # \<Sigma>) # st) \<rightarrow> State F H (Frame f l' 0 R \<Sigma> # st)" |

  step_call:
    "next_instr (F_get F) f l pc = Some (ICall g) \<Longrightarrow>
    F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma> \<Longrightarrow>
    list_all is_dyn_operand (take (arity gd) \<Sigma>) \<Longrightarrow>
    frame\<^sub>g = allocate_frame g gd (take (arity gd) \<Sigma>) (OpDyn uninitialized) \<Longrightarrow>
    State F H (Frame f l pc R\<^sub>f \<Sigma> # st) \<rightarrow> State F H (frame\<^sub>g # Frame f l pc R\<^sub>f \<Sigma> # st)" |

  step_return:
    "next_instr (F_get F) g l\<^sub>g pc\<^sub>g = Some IReturn \<Longrightarrow>
    F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma>\<^sub>f \<Longrightarrow>
    length \<Sigma>\<^sub>g = return gd \<Longrightarrow> list_all is_dyn_operand \<Sigma>\<^sub>g \<Longrightarrow>
    frame\<^sub>f' = Frame f l\<^sub>f (Suc pc\<^sub>f) R\<^sub>f (\<Sigma>\<^sub>g @ drop (arity gd) \<Sigma>\<^sub>f) \<Longrightarrow>
    State F H (Frame g l\<^sub>g pc\<^sub>g R\<^sub>g \<Sigma>\<^sub>g # Frame f l\<^sub>f pc\<^sub>f R\<^sub>f \<Sigma>\<^sub>f # st) \<rightarrow> State F H (frame\<^sub>f' # st)"

lemma step_deterministic:
  assumes "s1 \<rightarrow> s2" and "s1 \<rightarrow> s3"
  shows "s2 = s3"
  using assms
  apply (cases s1 s2 rule: step.cases)
  apply (auto simp: next_instr_length_instrs elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim!: step.cases dest: is_true_and_is_false_implies_False) [3]
  apply (auto simp: next_instr_length_instrs elim!: step.cases dest: is_true_and_is_false_implies_False) [1]
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

sublocale ubx_sem: semantics step "final F_get IReturn"
  using final_finished step_deterministic
  by unfold_locales

definition load where
  "load \<equiv> Global.load F_get (OpDyn uninitialized)"

sublocale inca_lang: language step "final F_get IReturn" load
  by unfold_locales

end

end
theory Multitape_Clock_Interface
  imports Multitape_Run_Facts
begin

section \<open>Exact unary clocks\<close>

text \<open>A small, construction-independent interface for clocks, as time
  hierarchy proofs use them.  A clock is tested on unary input, which a
  machine can write without first decoding a binary number.  The symbol \<open>3\<close>
  is part of the interface: a caller must establish that it belongs to the
  clock's input alphabet before using its initial configuration.

  The run is required to have exactly the displayed length and to end in the
  accepting state.  This is deliberately stronger than
  \<^const>\<open>accepts_in_time_ktm\<close>, which only asks for an accepting run of at
  most a given length and would therefore be satisfied by an immediately
  accepting machine for every budget.  Sink states supplied by
  \<^const>\<open>valid_ktm\<close> make the exact run a genuine alarm: it cannot have
  entered a terminal state early and then continued.

  This is the exact form of time constructibility, in which the clock's
  running time is the function itself.  It is close to what Hopcroft and
  Ullman \<^cite>\<open>"Hopcroft1979:introduction"\<close> call \<^emph>\<open>fully\<close>
  time-constructible, except that only one input of each length, the unary
  word, has to take exactly \<open>g n\<close> steps.

  The predicate says nothing about a value produced on a work tape.  That is
  intentional: what a hierarchy proof needs from it is an elapsed-time alarm.
  A contract for a clock that also writes its value has to state a tape layout
  and belongs with the development that uses it.\<close>

definition unary_word :: "nat \<Rightarrow> nat list" where
  "unary_word n = replicate n 3"

definition time_constructible :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "time_constructible g \<longleftrightarrow>
     (\<exists>D :: (nat, nat) ktm.
        well_formed_ktm D \<and> det_ktm D \<and>
        3 \<in> Sigma_ktm D \<and>
        (\<forall>n. \<exists>cfg. (init_config_ktm D (unary_word n), cfg)
                      \<in> (ktm_step (delta_ktm D)) ^^ (g n)
                   \<and> ktc_state cfg = t_ktm D))"

lemma unary_word_length [simp]: "length (unary_word n) = n"
  by (simp add: unary_word_def)

lemma unary_word_set [simp]: "set (unary_word n) = (if n = 0 then {} else {3})"
proof (induct n)
  case 0
  then show ?case by (simp add: unary_word_def)
next
  case (Suc n)
  then show ?case by (simp add: unary_word_def)
qed

lemma unary_word_subset:
  assumes "3 \<in> Sigma_ktm M"
  shows "set (unary_word n) \<subseteq> Sigma_ktm M"
  using assms by (auto simp: unary_word_def)

subsection \<open>Halting states are sinks\<close>

text \<open>The exact-alarm interface is useful only when its terminal run cannot
  pass through a halting state early.  Validity supplies that sink property
  for every multitape machine, and the following lemmas package the generic
  consequences that a clocked construction uses.  The first is the
  contrapositive of the substrate's \<open>ktm_step_src\<close>, in the form these
  proofs consume it.  They mention no particular
  construction.\<close>

lemma halt_state_sink:
  assumes vM: "valid_ktm M" and halt: "ktc_state c \<in> {t_ktm M, r_ktm M}"
  shows "(c, c') \<notin> ktm_step (delta_ktm M)"
  using halt ktm_step_src_neq_t [OF vM] ktm_step_src_neq_r [OF vM] by blast

lemma halt_no_further:
  assumes vM: "valid_ktm M"
      and halt: "ktc_state c \<in> {t_ktm M, r_ktm M}"
      and pos: "0 < N"
  shows "(c, c') \<notin> (ktm_step (delta_ktm M)) ^^ N"
proof
  assume run: "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ N"
  from pos obtain m where m: "N = Suc m" by (cases N) auto
  from run [unfolded m] obtain d where "(c, d) \<in> ktm_step (delta_ktm M)"
    by (blast dest: relpow_Suc_D2)
  with halt_state_sink [OF vM halt] show False by simp
qed

lemma alarm_running_lt:
  assumes vM: "valid_ktm M" and det: "det_ktm M"
      and alarm: "(c\<^sub>0, cfg) \<in> (ktm_step (delta_ktm M)) ^^ G"
      and halt: "ktc_state cfg = t_ktm M"
      and run: "(c\<^sub>0, c) \<in> (ktm_step (delta_ktm M)) ^^ m"
      and alive: "ktc_state c \<noteq> t_ktm M" "ktc_state c \<noteq> r_ktm M"
    shows "m < G"
proof (rule ccontr)
  let ?R = "ktm_step (delta_ktm M)"
  assume "\<not> m < G"
  then have "m = G + (m - G)" by simp
  with run have "(c\<^sub>0, c) \<in> ?R ^^ G O ?R ^^ (m - G)" by (metis relpow_add)
  then obtain y where ay: "(c\<^sub>0, y) \<in> ?R ^^ G" and yc: "(y, c) \<in> ?R ^^ (m - G)"
    by auto
  from det_ktm_relpow_unique [OF det ay alarm] have y: "y = cfg" .
  with halt have yhalt: "ktc_state y \<in> {t_ktm M, r_ktm M}" by simp
  show False
  proof (cases "m - G")
    case 0
    with yc have "c = y" by simp
    with yhalt alive show False by simp
  next
    case (Suc r)
    then have "0 < m - G" by simp
    from halt_no_further [OF vM yhalt this] yc show False by simp
  qed
qed

lemma alarm_start_alive:
  assumes vM: "valid_ktm M"
      and run: "(init_config_ktm M v, cfg) \<in> (ktm_step (delta_ktm M)) ^^ G"
      and G: "0 < G"
    shows "s_ktm M \<noteq> t_ktm M \<and> s_ktm M \<noteq> r_ktm M"
proof (rule ccontr)
  assume "\<not> (s_ktm M \<noteq> t_ktm M \<and> s_ktm M \<noteq> r_ktm M)"
  then have "ktc_state (init_config_ktm M v) \<in> {t_ktm M, r_ktm M}"
    by (cases M) simp
  from halt_no_further [OF vM this G] run show False by simp
qed

end

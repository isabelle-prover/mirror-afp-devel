(*
  File:      Example_SOL.thy
  Author:    Anders Schlichtkrull
  Author:    Asta Halkjær Boserup

*)

chapter \<open>Example: Second-Order Logic\<close>

text \<open>Generalizes \<^cite>\<open>"FOL-Axiomatic-AFP"\<close> and \<^cite>\<open>"From21-TYPES"\<close>
      from first-order logic to second-order logic\<close>

theory Example_SOL imports
  Abstract_Consistency_Property
begin

section \<open>Syntax\<close>

datatype (params_sym:'f) sym
  = VarS nat (\<open>\<^bold>#\<^sub>2\<close>)
  | SymS 'f (\<open>\<^bold>\<circle>\<^sub>2\<close>)

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun \<open>'f sym\<close> \<open>'f tm list\<close> (\<open>\<^bold>\<circle>\<close>)
  | Cst 'f (\<open>\<^bold>\<star>\<close>) 

datatype (params_fm: 'f) fm
  = Falsity (\<open>\<^bold>\<bottom>\<close>)
  | is_Pre: Pre \<open>'f sym\<close> \<open>'f tm list\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>'f fm\<close> \<open>'f fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>'f fm\<close> (\<open>\<^bold>\<forall>\<close>)
  | UniP \<open>'f fm\<close> (\<open>\<^bold>\<forall>\<^sub>P\<close>)
  | UniF \<open>'f fm\<close> (\<open>\<^bold>\<forall>\<^sub>F\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation And (infix \<open>\<^bold>\<and>\<close> 50) where \<open>p \<^bold>\<and> q \<equiv> \<^bold>\<not> (p \<^bold>\<longrightarrow> \<^bold>\<not> q)\<close>

abbreviation Iff (infix \<open>\<^bold>\<longleftrightarrow>\<close> 50) where \<open>p \<^bold>\<longleftrightarrow> q \<equiv> (p \<^bold>\<longrightarrow> q) \<^bold>\<and> (q \<^bold>\<longrightarrow> p)\<close>

abbreviation Eql (\<open>_ \<^bold>= _\<close>) where \<open>t1 \<^bold>= t2 \<equiv> (\<^bold>\<forall>\<^sub>P ((\<^bold>\<cdot>(\<^bold>#\<^sub>2 0) [t1]) \<^bold>\<longleftrightarrow> (\<^bold>\<cdot>(\<^bold>#\<^sub>2 0) [t2])))\<close>

abbreviation ExiF (\<open>\<^bold>\<exists>\<^sub>F\<close>) where \<open>\<^bold>\<exists>\<^sub>F p \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sub>F(\<^bold>\<not>p))\<close>

abbreviation ExiP (\<open>\<^bold>\<exists>\<^sub>P\<close>) where \<open>\<^bold>\<exists>\<^sub>P p \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sub>P(\<^bold>\<not>p))\<close>

term \<open>\<^bold>\<forall>(\<^bold>\<bottom> \<^bold>\<longrightarrow> (\<^bold>\<cdot>(\<^bold>\<circle>\<^sub>2 ''P'') [\<^bold>\<circle>(\<^bold>\<circle>\<^sub>2 ''f'') [\<^bold>#0]]))\<close>

section \<open>Semantics\<close>

definition shift (\<open>_\<langle>_:_\<rangle>\<close>) where
  \<open>E\<langle>n:x\<rangle> m \<equiv> if m < n then E m else if m = n then x else E (m-1)\<close>

primrec semantics_fn (\<open>\<lblot>_, _\<rblot>\<^sub>2\<close>) where
  \<open>\<lblot>E\<^sub>F, F\<rblot>\<^sub>2 (\<^bold>#\<^sub>2 n) = E\<^sub>F n\<close>
| \<open>\<lblot>E\<^sub>F, F\<rblot>\<^sub>2 (\<^bold>\<circle>\<^sub>2 f) = F f\<close>

primrec semantics_tm (\<open>\<lblot>_,_, _, _\<rblot>\<close>) where
  \<open>\<lblot>E, E\<^sub>F, C, F\<rblot> (\<^bold>#n) = E n\<close>
| \<open>\<lblot>E, E\<^sub>F, C, F\<rblot> (\<^bold>\<circle>f ts) = (\<lblot>E\<^sub>F, F\<rblot>\<^sub>2 f) (map \<lblot>E, E\<^sub>F, C, F\<rblot> ts)\<close>
| \<open>\<lblot>E, E\<^sub>F, C, F\<rblot> (\<^bold>\<star> c) = C c\<close>

fun semantics_fm (infix \<open>\<Turnstile>\<close> 50) where
  \<open>((_, _, _, _, _, _, _, _) \<Turnstile> \<^bold>\<bottom>) = False\<close>
| \<open>((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> \<^bold>\<cdot>P ts) = \<lblot>E\<^sub>P, G\<rblot>\<^sub>2 P (map \<lblot>E, E\<^sub>F, C, F\<rblot> ts)\<close>
| \<open>((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p \<^bold>\<longrightarrow> q) = ((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p \<longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> q)\<close>
| \<open>((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> \<^bold>\<forall>p) = (\<forall>x. (E\<langle>0:x\<rangle>, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p)\<close>
| \<open>((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> \<^bold>\<forall>\<^sub>Pp) = (\<forall>x \<in> PS. (E, E\<^sub>F, E\<^sub>P\<langle>0:x\<rangle>, C, F, G, PS, FS) \<Turnstile> p)\<close>
| \<open>((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> \<^bold>\<forall>\<^sub>Fp) = (\<forall>x \<in> FS. (E, E\<^sub>F\<langle>0:x\<rangle>, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p)\<close>

proposition \<open>(E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> (\<^bold>\<forall>(\<^bold>\<cdot>P [\<^bold># 0]) \<^bold>\<longrightarrow> \<^bold>\<cdot>P [\<^bold>\<star>a])\<close>
  by (simp add: shift_def)

section \<open>Operations\<close>

subsection \<open>Shift\<close>

context fixes n m :: nat begin

lemma shift_eq [simp]: \<open>n = m \<Longrightarrow> E\<langle>n:x\<rangle> m = x\<close>
  by (simp add: shift_def)

lemma shift_gt [simp]: \<open>m < n \<Longrightarrow> E\<langle>n:x\<rangle> m = E m\<close>
  by (simp add: shift_def)

lemma shift_lt [simp]: \<open>n < m \<Longrightarrow> E\<langle>n:x\<rangle> m = E (m-1)\<close>
  by (simp add: shift_def)

lemma shift_commute [simp]: \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>)\<close>
proof
  fix m
  show \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) m = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>) m\<close>
    unfolding shift_def by (cases m) simp_all
qed

end

subsection \<open>Parameters\<close>

abbreviation \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

lemma upd_params_sym [simp]: \<open>f \<notin> params_sym fn \<Longrightarrow> \<lblot>E\<^sub>F, F(f := x)\<rblot>\<^sub>2 fn = \<lblot>E\<^sub>F, F\<rblot>\<^sub>2 fn\<close>
  by (induct fn) (auto cong: map_cong)

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lblot>E, E\<^sub>F, C, F(f := x)\<rblot> t = \<lblot>E, E\<^sub>F, C, F\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_tm_c [simp]: \<open>c \<notin> params_tm t \<Longrightarrow> \<lblot>E, E\<^sub>F, C(c := x), F\<rblot> t = \<lblot>E, E\<^sub>F, C, F\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F(f := x), G, PS, FS) \<Turnstile> p \<longleftrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  by (induct p arbitrary: E E\<^sub>P E\<^sub>F) (auto cong: map_cong)

lemma upd_params_fm_c [simp]: \<open>c \<notin> params_fm p \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C(c := x), F, G, PS, FS) \<Turnstile> p \<longleftrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  by (induct p arbitrary: E E\<^sub>P E\<^sub>F) (auto cong: map_cong)

lemma upd_params_fm_G [simp]: \<open>P \<notin> params_fm p \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G(P := x), PS, FS) \<Turnstile> p \<longleftrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  by (induct p arbitrary: E E\<^sub>F E\<^sub>P) (auto cong: map_cong)

lemma finite_params_sym [simp]: \<open>finite (params_sym fn)\<close>
  by (induct fn) simp_all

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all


subsection \<open>Instantiation\<close>

primrec lift_tm (\<open>\<^bold>\<up>\<close>) where
  \<open>\<^bold>\<up>(\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<circle>f ts) = \<^bold>\<circle>f (map \<^bold>\<up> ts)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<star>c) = \<^bold>\<star> c\<close>

primrec lift_sym (\<open>\<^bold>\<up>\<^sub>2\<close>) where
  \<open>\<^bold>\<up>\<^sub>2(\<^bold>#\<^sub>2 n) = \<^bold>#\<^sub>2 (n+1)\<close>
| \<open>\<^bold>\<up>\<^sub>2(\<^bold>\<circle>\<^sub>2 p) = \<^bold>\<circle>\<^sub>2 p\<close>

primrec lift_fn (\<open>\<^bold>\<up>\<^sub>F\<close>) where
  \<open>\<^bold>\<up>\<^sub>F(\<^bold>#n) = \<^bold>#n\<close>
| \<open>\<^bold>\<up>\<^sub>F(\<^bold>\<circle>f ts) = \<^bold>\<circle>(\<^bold>\<up>\<^sub>2 f) (map \<^bold>\<up>\<^sub>F ts)\<close>
| \<open>\<^bold>\<up>\<^sub>F(\<^bold>\<star> c) = \<^bold>\<star> c\<close>

primrec inst_tm (\<open>\<llangle>_'/_\<rrangle>\<close>) where
  \<open>\<llangle>s/m\<rrangle>(\<^bold>#n) = (if n < m then \<^bold>#n else if n = m then s else \<^bold>#(n-1))\<close>
| \<open>\<llangle>s/m\<rrangle>(\<^bold>\<circle>f ts) = \<^bold>\<circle>f (map \<llangle>s/m\<rrangle> ts)\<close>
| \<open>\<llangle>s/m\<rrangle>(\<^bold>\<star>c) = \<^bold>\<star>c\<close>

primrec inst_sym (\<open>\<llangle>_'/_\<rrangle>\<^sub>2\<close>) where
  \<open>\<llangle>s/m\<rrangle>\<^sub>2 (\<^bold>#\<^sub>2 n) = (if n < m then \<^bold>#\<^sub>2 n else if n = m then s else \<^bold>#\<^sub>2 (n-1))\<close>
| \<open>\<llangle>s/m\<rrangle>\<^sub>2 (\<^bold>\<circle>\<^sub>2 p) = \<^bold>\<circle>\<^sub>2 p\<close>

primrec inst_fn (\<open>\<llangle>_'/_\<rrangle>\<^sub>F\<close>) where
  \<open>\<llangle>s/m\<rrangle>\<^sub>F(\<^bold>#n) = (\<^bold>#n)\<close>
| \<open>\<llangle>s/m\<rrangle>\<^sub>F(\<^bold>\<circle>f ts) = \<^bold>\<circle>(\<llangle>s/m\<rrangle>\<^sub>2 f) (map \<llangle>s/m\<rrangle>\<^sub>F ts)\<close>
| \<open>\<llangle>s/m\<rrangle>\<^sub>F(\<^bold>\<star>c) = (\<^bold>\<star>c)\<close>

primrec inst_fm (\<open>\<langle>_'/_\<rangle>\<close>) where
  \<open>\<langle>_/_\<rangle>\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map \<llangle>s/m\<rrangle> ts)\<close>
| \<open>\<langle>s/m\<rangle>(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>p \<^bold>\<longrightarrow> \<langle>s/m\<rangle>q\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>\<^bold>\<up>s/m+1\<rangle>p)\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>\<^sub>Pp) = \<^bold>\<forall>\<^sub>P(\<langle>s/m\<rangle>p)\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>\<^sub>Fp) = \<^bold>\<forall>\<^sub>F(\<langle>\<^bold>\<up>\<^sub>F s/m\<rangle>p)\<close>

primrec inst_fm_P (\<open>\<langle>_'/_\<rangle>\<^sub>P\<close>) where
  \<open>\<langle>_/_\<rangle>\<^sub>P\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>P(\<^bold>\<cdot>P ts) = \<^bold>\<cdot>(\<llangle>s/m\<rrangle>\<^sub>2 P) ts\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>P(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>\<^sub>Pp \<^bold>\<longrightarrow> \<langle>s/m\<rangle>\<^sub>Pq\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>P(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>s/m\<rangle>\<^sub>Pp)\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>P(\<^bold>\<forall>\<^sub>Pp) = \<^bold>\<forall>\<^sub>P(\<langle>\<^bold>\<up>\<^sub>2 s/m+1\<rangle>\<^sub>Pp)\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>P(\<^bold>\<forall>\<^sub>Fp) = \<^bold>\<forall>\<^sub>F(\<langle>s/m\<rangle>\<^sub>Pp)\<close>

primrec inst_fm_F (\<open>\<langle>_'/_\<rangle>\<^sub>F\<close>) where
  \<open>\<langle>_/_\<rangle>\<^sub>F\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>F(\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map \<llangle>s/m\<rrangle>\<^sub>F ts)\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>F(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>\<^sub>Fp \<^bold>\<longrightarrow> \<langle>s/m\<rangle>\<^sub>Fq\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>F(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>s/m\<rangle>\<^sub>Fp)\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>F(\<^bold>\<forall>\<^sub>Pp) = \<^bold>\<forall>\<^sub>P(\<langle>s/m\<rangle>\<^sub>Fp)\<close>
| \<open>\<langle>s/m\<rangle>\<^sub>F(\<^bold>\<forall>\<^sub>Fp) = \<^bold>\<forall>\<^sub>F(\<langle>\<^bold>\<up>\<^sub>2 s/m+1\<rangle>\<^sub>Fp)\<close>

lemma lift_lemma [simp]: \<open>\<lblot>E\<langle>0:x\<rangle>, E\<^sub>F, C, F\<rblot> (\<^bold>\<up>t) = \<lblot>E, E\<^sub>F, C, F\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma lift_lemma_P [simp]: \<open>\<lblot>E\<^sub>P\<langle>0:x\<rangle>, G\<rblot>\<^sub>2 (\<^bold>\<up>\<^sub>2 P) = \<lblot>E\<^sub>P, G\<rblot>\<^sub>2 P\<close>
  by (induct P) (auto cong: map_cong)

lemma lift_lemma_F [simp]: \<open>\<lblot>E, E\<^sub>F\<langle>0:x\<rangle>, C, F\<rblot> (\<^bold>\<up>\<^sub>F tm) = \<lblot>E, E\<^sub>F, C, F\<rblot> tm\<close>
  by (induct tm) (auto cong: map_cong)

lemma inst_tm_semantics [simp]: \<open>\<lblot>E, E\<^sub>F, C, F\<rblot> (\<llangle>s/m\<rrangle>t) = \<lblot>E\<langle>m:\<lblot>E, E\<^sub>F, C, F\<rblot> s\<rangle>, E\<^sub>F, C, F\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_sym_semantics [simp]: \<open>\<lblot>E\<^sub>F, G\<rblot>\<^sub>2 (\<llangle>s/m\<rrangle>\<^sub>2 fn) = \<lblot>E\<^sub>F\<langle>m:\<lblot>E\<^sub>F, G\<rblot>\<^sub>2 s\<rangle>, G\<rblot>\<^sub>2 fn\<close>
  by (induct fn) (auto cong: map_cong)

lemma inst_tm_semantics_F [simp]: \<open>\<lblot>E, E\<^sub>F, C, F\<rblot> (\<llangle>s/m\<rrangle>\<^sub>F t) = \<lblot>E, E\<^sub>F\<langle>m:\<lblot>E\<^sub>F, F\<rblot>\<^sub>2 s\<rangle>, C, F\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_fm_semantics_F [simp]:
   \<open>(E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> (\<langle>t/m\<rangle>\<^sub>F p) \<longleftrightarrow> (E, E\<^sub>F\<langle>m:\<lblot>E\<^sub>F, F\<rblot>\<^sub>2 t\<rangle>, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  by (induct p arbitrary: E E\<^sub>P E\<^sub>F m t) (auto cong: map_cong)

lemma inst_fm_semantics [simp]:
   \<open>(E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> (\<langle>t/m\<rangle>p) \<longleftrightarrow> (E\<langle>m:\<lblot>E, E\<^sub>F, C, F\<rblot> t\<rangle>, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  by (induct p arbitrary: E E\<^sub>P E\<^sub>F m t) (auto cong: map_cong)

lemma inst_fm_semantics_P [simp]: \<open>(E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> (\<langle>P/m\<rangle>\<^sub>Pp) \<longleftrightarrow> (E, E\<^sub>F, E\<^sub>P\<langle>m:\<lblot>E\<^sub>P, G\<rblot>\<^sub>2 P\<rangle>, C, F, G, PS, FS) \<Turnstile> p\<close>
  by (induct p arbitrary: E E\<^sub>F E\<^sub>P m P) (auto cong: map_cong)

subsection \<open>Size\<close>

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<cdot>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>
| \<open>size_fm (\<^bold>\<forall>\<^sub>Pp) = 1 + size_fm p\<close>
| \<open>size_fm (\<^bold>\<forall>\<^sub>Fp) = 1 + size_fm p\<close>

lemma size_inst_fm [simp]: \<open>size_fm (\<langle>t/m\<rangle>p) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all

lemma size_inst_fm_P [simp]: \<open>size_fm (\<langle>t/m\<rangle>\<^sub>Pp) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all

lemma size_inst_fm_F [simp]: \<open>size_fm (\<langle>t/m\<rangle>\<^sub>Fp) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all


section \<open>Model Existence\<close>

inductive confl_class :: \<open>'f fm list \<Rightarrow> 'f fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFls: \<open>[ \<^bold>\<bottom> ] \<leadsto>\<^sub>\<crossmark> [ \<^bold>\<bottom> ]\<close>
| CNeg: \<open>[ \<^bold>\<not> (\<^bold>\<cdot>P ts) ] \<leadsto>\<^sub>\<crossmark> [ \<^bold>\<cdot>P ts ]\<close>

inductive alpha_class :: \<open>'f fm list \<Rightarrow> 'f fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
  CImpN: \<open>[ \<^bold>\<not> (p \<^bold>\<longrightarrow> q) ] \<leadsto>\<^sub>\<alpha> [ p, \<^bold>\<not> q ]\<close>

inductive beta_class :: \<open>'f fm list \<Rightarrow> 'f fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CImpP: \<open>[ p \<^bold>\<longrightarrow> q ] \<leadsto>\<^sub>\<beta> [ \<^bold>\<not> p, q ]\<close>

inductive gamma_class :: \<open>'f fm list \<Rightarrow>  ('f tm \<Rightarrow> 'f fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CAllP: \<open>[ \<^bold>\<forall>p ] \<leadsto>\<^sub>\<gamma> (\<lambda>t. [ \<langle>t/0\<rangle>p ])\<close>

inductive gamma_class_P :: \<open>'f fm list \<Rightarrow> ('f sym \<Rightarrow> 'f fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>P\<close> 50) where
  CAllPP: \<open>[ \<^bold>\<forall>\<^sub>P p ] \<leadsto>\<^sub>\<gamma>\<^sub>P (\<lambda>s. [ \<langle>s/0\<rangle>\<^sub>P p ])\<close>

inductive gamma_class_F :: \<open>'f fm list \<Rightarrow> ('f sym \<Rightarrow> 'f fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>F\<close> 50) where
  CAllFP: \<open>[ \<^bold>\<forall>\<^sub>F p ] \<leadsto>\<^sub>\<gamma>\<^sub>F (\<lambda>s. [ \<langle>s/0\<rangle>\<^sub>F p ])\<close>

fun \<delta> :: \<open>'f fm \<Rightarrow> 'f \<Rightarrow> 'f fm list\<close> where
  CAllN:   \<open>\<delta> (\<^bold>\<not> \<^bold>\<forall>p) x = [ \<^bold>\<not> \<langle>\<^bold>\<star>x/0\<rangle> p ]\<close> 
| CAll2PN: \<open>\<delta> (\<^bold>\<not> \<^bold>\<forall>\<^sub>P p) x = [ \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>\<^sub>P p ]\<close>
| CAll2FN: \<open>\<delta> ( \<^bold>\<not> \<^bold>\<forall>\<^sub>F p ) x = [ \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>\<^sub>F p ]\<close>
| NOMATCH: \<open>\<delta> _ _ = []\<close>

interpretation P: Params map_fm params_fm \<open>\<lambda>_. True\<close>
  by unfold_locales (auto simp: tm.map_id0 fm.map_id0 cong: tm.map_cong0 fm.map_cong0)

interpretation C: Confl map_fm params_fm \<open>\<lambda>_. True\<close> confl_class
  by unfold_locales (auto elim!: confl_class.cases intro: confl_class.intros)

interpretation A: Alpha map_fm params_fm \<open>\<lambda>_. True\<close> alpha_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: alpha_class.cases intro: alpha_class.intros)

interpretation B: Beta map_fm params_fm \<open>\<lambda>_. True\<close> beta_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: beta_class.cases intro: beta_class.intros)

lemma map_tm_inst_tm [simp]:
  "map_tm f (\<llangle>t/n\<rrangle> x) = \<llangle>map_tm f t/n\<rrangle> (map_tm f x)"
  by (induct x) simp_all

lemma map_tm_lift_tm [simp]: "map_tm f (\<^bold>\<up> t) = \<^bold>\<up> (map_tm f t)"
  by (induct t) simp_all

lemma map_sym_lift_fn [simp]: \<open>map_sym f (\<^bold>\<up>\<^sub>2 t) = \<^bold>\<up>\<^sub>2 (map_sym f t)\<close>
  by (induct t) auto

lemma map_tm_lift_fn [simp]: "map_tm f (\<^bold>\<up>\<^sub>F t) = \<^bold>\<up>\<^sub>F (map_tm f t)"
  by (induct t) simp_all

lemma map_fm_inst_single [simp]: \<open>map_fm f (\<langle>t/m\<rangle>p) = \<langle>map_tm f t/m\<rangle>(map_fm f p)\<close>
  by (induct p arbitrary: t m) simp_all

lemma map_sym_inst_sym [simp]: \<open>map_sym f (\<llangle>t/m\<rrangle>\<^sub>2 p) = \<llangle>map_sym f t/m\<rrangle>\<^sub>2 (map_sym f p)\<close>
  by (induct p arbitrary: t m) simp_all

lemma psub_inst_single' [simp]: \<open>map_fm f (\<langle>t/m\<rangle>\<^sub>P p) = \<langle>map_sym f t/m\<rangle>\<^sub>P(map_fm f p)\<close>
  by (induct p arbitrary: t m) simp_all

lemma map_tm_inst_fn [simp]: \<open>map_tm f (\<llangle>t/m\<rrangle>\<^sub>F s) = \<llangle>map_sym f t/m\<rrangle>\<^sub>F (map_tm f s)\<close>
  by (induct s) auto

lemma psub_inst_single'' [simp]: \<open>map_fm f (\<langle>t/m\<rangle>\<^sub>F p) = \<langle>map_sym f t/m\<rangle>\<^sub>F(map_fm f p)\<close>
  by (induct p arbitrary: t m) simp_all

interpretation G: Gamma_UNIV map_tm map_fm params_fm \<open>\<lambda>_. True\<close> gamma_class
  by unfold_locales (fastforce elim: gamma_class.cases intro: gamma_class.intros)+

interpretation G\<^sub>P: Gamma_UNIV map_sym map_fm params_fm \<open>\<lambda>_. True\<close> gamma_class_P
  by unfold_locales (fastforce elim: gamma_class_P.cases intro: gamma_class_P.intros)+

interpretation G\<^sub>F: Gamma_UNIV map_sym map_fm params_fm \<open>\<lambda>_. True\<close> gamma_class_F
  by unfold_locales (fastforce elim: gamma_class_F.cases intro: gamma_class_F.intros)+

interpretation D: Delta map_fm params_fm \<open>\<lambda>_. True\<close> \<delta>
proof
  show \<open>\<And>f. \<delta> (map_fm f p) (f x) = map (map_fm f) (\<delta> p x)\<close> for p :: \<open>'x fm\<close> and x
    by (induct p x rule: \<delta>.induct) simp_all
qed

abbreviation Kinds :: \<open>('x, 'x fm) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, G\<^sub>P.kind, G\<^sub>F.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>P.sat\<^sub>E C.kind C\<close> \<open>P.sat\<^sub>E A.kind C\<close> \<open>P.sat\<^sub>E B.kind C\<close> \<open>P.sat\<^sub>E G.kind C\<close> \<open>P.sat\<^sub>E G\<^sub>P.kind C\<close>
    \<open>P.sat\<^sub>E G\<^sub>F.kind C\<close> \<open>P.sat\<^sub>E D.kind C\<close>
  shows \<open>P.prop\<^sub>E Kinds C\<close>
  unfolding P.prop\<^sub>E_def using assms by simp

interpretation Consistency_Kinds map_fm params_fm \<open>\<lambda>_. True\<close> Kinds
  using P.Params_axioms C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    G.Consistency_Kind_axioms G\<^sub>P.Consistency_Kind_axioms G\<^sub>F.Consistency_Kind_axioms
    D.Consistency_Kind_axioms
  by (auto intro: Consistency_Kinds.intro simp: Consistency_Kinds_axioms_def)

interpretation Maximal_Consistency map_fm params_fm \<open>\<lambda>_. True\<close> Kinds
proof
  show \<open>infinite (UNIV :: 'x fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed simp

abbreviation henv\<^sub>P where "henv\<^sub>P H == \<lambda>n ts. \<^bold>\<cdot>(\<^bold>#\<^sub>2 n) ts \<in> H"

abbreviation hpred where "hpred H == \<lambda>P ts. \<^bold>\<cdot>(\<^bold>\<circle>\<^sub>2 P) ts \<in> H"

abbreviation hdom\<^sub>P where "hdom\<^sub>P H == range (henv\<^sub>P H) \<union> range (hpred H)"

abbreviation henv\<^sub>F where "henv\<^sub>F == \<lambda>f. \<^bold>\<circle> (\<^bold>#\<^sub>2 f)"

abbreviation hfun where "hfun ==  \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2 f)"

definition hdom\<^sub>F where "hdom\<^sub>F == range henv\<^sub>F \<union> range hfun"

abbreviation (input) hmodel (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>H\<rbrakk> \<equiv> (\<^bold>#, henv\<^sub>F, henv\<^sub>P H, \<^bold>\<star>, hfun, hpred H, hdom\<^sub>P H, hdom\<^sub>F)\<close>

lemma semantics_tm_id [simp]: \<open>\<lblot>\<^bold>#, henv\<^sub>F , \<^bold>\<star> , \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2 f) \<rblot> t = t\<close>
proof (induct t)
  case (Var x)
  then show ?case 
    by (auto cong: map_cong)
next
  case (Fun x1a x2)
  then show ?case
    by (cases x1a) (auto cong: map_cong)
next
  case (Cst c)
  then show ?case
    by auto
qed

lemma semantics_tm_id_map [simp]: \<open>map \<lblot>\<^bold>#, \<lambda>f. \<^bold>\<circle> (\<^bold>#\<^sub>2 f) , \<^bold>\<star>, \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2 f) \<rblot> ts = ts\<close>
  by (auto cong: map_cong)

lemma semantics_fn_h [simp]: \<open>\<lblot>henv\<^sub>P S, hpred S\<rblot>\<^sub>2 P ts \<longleftrightarrow> \<^bold>\<cdot>P ts \<in> S\<close>
  by (cases P) simp_all

lemma canonical_henv\<^sub>P:
  \<open>\<forall>t. (\<^bold>#, henv\<^sub>F, (henv\<^sub>P S)\<langle>0:\<lblot>henv\<^sub>P S, hpred S\<rblot>\<^sub>2 t\<rangle>, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p \<Longrightarrow>
       (\<^bold>#, henv\<^sub>F, (henv\<^sub>P S)\<langle>0:henv\<^sub>P S n\<rangle>, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p\<close>
  by (metis semantics_fn.simps(1))

lemma canonical_hpred:
  \<open>\<forall>t. (\<^bold>#, henv\<^sub>F, (henv\<^sub>P S)\<langle>0:\<lblot>henv\<^sub>P S, hpred S\<rblot>\<^sub>2 t\<rangle>, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p \<Longrightarrow>
       (\<^bold>#, henv\<^sub>F, (henv\<^sub>P S)\<langle>0:hpred S P\<rangle>, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p\<close>
  by (metis semantics_fn.simps(2))

lemma canonical_henv\<^sub>F:
  \<open>\<forall>t. (\<^bold>#, henv\<^sub>F\<langle>0:\<lblot>henv\<^sub>F, hfun\<rblot>\<^sub>2 t\<rangle>, henv\<^sub>P S, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p \<Longrightarrow>
       (\<^bold>#, henv\<^sub>F\<langle>0:henv\<^sub>F f\<rangle>, henv\<^sub>P S, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p\<close>
  by (metis semantics_fn.simps(1))

lemma canonical_hfun:
  \<open>\<forall>t. (\<^bold>#, henv\<^sub>F\<langle>0:\<lblot>henv\<^sub>F, hfun\<rblot>\<^sub>2 t\<rangle>, henv\<^sub>P S, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p \<Longrightarrow>
       (\<^bold>#, henv\<^sub>F\<langle>0:hfun f\<rangle>, henv\<^sub>P S, \<^bold>\<star>, hfun, hpred S, hdom\<^sub>P S, hdom\<^sub>F) \<Turnstile> p\<close>
  by (metis semantics_fn.simps(2))

locale MyHintikka = Hintikka map_fm params_fm \<open>\<lambda>_. True\<close> Kinds S for S :: \<open>'x fm set\<close>
begin

lemmas
  confl = sat\<^sub>H[of C.kind] and
  alpha = sat\<^sub>H[of A.kind] and
  beta = sat\<^sub>H[of B.kind] and
  gammaFO = sat\<^sub>H[of G.kind] and
  gamma2P = sat\<^sub>H[of G\<^sub>P.kind] and
  gamma2F = sat\<^sub>H[of G\<^sub>F.kind] and
  delta = sat\<^sub>H[of D.kind]

theorem model: \<open>(p \<in> S \<longrightarrow> \<lbrakk>S\<rbrakk> \<Turnstile> p) \<and> (\<^bold>\<not> p \<in> S \<longrightarrow> \<not> \<lbrakk>S\<rbrakk> \<Turnstile> p)\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
  proof (cases x)
    case Falsity
    then show ?thesis
      using confl by (force intro: CFls)
  next
    case (Pre P ts)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<cdot>P ts\<close> \<open>\<^bold>\<cdot>P ts \<in> S\<close>
      then show \<open>\<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<cdot>P ts)\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<cdot>P ts\<close> \<open>\<^bold>\<not> \<^bold>\<cdot>P ts \<in> S\<close>
      then have \<open>\<^bold>\<cdot>P ts \<notin> S\<close>
        using confl by (force intro: CNeg)
      then show \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<cdot>P ts)\<close>
        by simp
    qed
  next
    case (Imp p q)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>p \<^bold>\<longrightarrow> q \<in> S\<close>
      then have \<open>\<^bold>\<not> p \<in> S \<or> q \<in> S\<close>
        using beta by (force intro: CImpP)
      then show \<open>\<lbrakk>S\<rbrakk> \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
        using 2 Imp by auto
    next
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> S\<close>
      then have \<open>p \<in> S \<and> \<^bold>\<not> q \<in> S\<close>
        using alpha by (force intro: CImpN)
      then show \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
        using 2 Imp by auto
    qed
  next
    case (Uni p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<forall>p \<in> S\<close>
      then have \<open>\<forall>t. \<langle>t/0\<rangle>p \<in> S\<close>
        using gammaFO by (fastforce intro: CAllP)
      moreover have \<open>\<forall>t. (\<langle>t/0\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. \<lbrakk>S\<rbrakk> \<Turnstile> (\<langle>t/0\<rangle>p)\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>\<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<forall>p)\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<in> S\<close>
        using delta by auto
      moreover have \<open>(\<langle>\<^bold>\<star>a/0\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<langle>\<^bold>\<star>a/0\<rangle>p)\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<forall>p)\<close>
        by auto
    qed
  next
    case (UniP p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>\<^sub>P p\<close> \<open>\<^bold>\<forall>\<^sub>P p \<in> S\<close>
      then have \<open>\<forall>t. \<langle>t/0\<rangle>\<^sub>P p \<in> S\<close>
        using gamma2P by (fastforce intro: CAllPP)
      moreover have *: \<open>\<forall>t. (\<langle>t/0\<rangle>\<^sub>P p, \<^bold>\<forall>\<^sub>P p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. \<lbrakk>S\<rbrakk> \<Turnstile> (\<langle>t/0\<rangle>\<^sub>P p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>P p\<close> by blast
      then show \<open>\<lbrakk>S\<rbrakk> \<Turnstile> \<^bold>\<forall>\<^sub>P p\<close>
        using canonical_henv\<^sub>P canonical_hpred by auto
    next
      assume \<open>x = \<^bold>\<forall>\<^sub>P p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>P p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>P p \<in> S\<close>
        using delta by auto
      moreover have \<open>(\<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>P p, \<^bold>\<forall>\<^sub>P p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<langle>\<^bold>\<circle>\<^sub>2a/0\<rangle>\<^sub>P p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>P p\<close> by blast
      then show \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<forall>\<^sub>P p)\<close>
        by auto
    qed
  next
    case (UniF p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>\<^sub>F p\<close> \<open>\<^bold>\<forall>\<^sub>F p \<in> S\<close>
      then have \<open>\<forall>t. \<langle>t/0\<rangle>\<^sub>F p \<in> S\<close>
        using gamma2F by (fastforce intro: CAllFP)
      moreover have \<open>\<forall>t. (\<langle>t/0\<rangle>\<^sub>F p, \<^bold>\<forall>\<^sub>F p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. \<lbrakk>S\<rbrakk> \<Turnstile> (\<langle>t/0\<rangle>\<^sub>F p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>F p\<close> by blast
      then show \<open>\<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<forall>\<^sub>F p)\<close>
        using canonical_henv\<^sub>F canonical_hfun unfolding hdom\<^sub>F_def by auto
    next
      assume \<open>x = \<^bold>\<forall>\<^sub>F p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>F p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>F p \<in> S\<close>
        using delta by auto
      moreover have \<open>(\<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>F p, \<^bold>\<forall>\<^sub>F p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<langle>\<^bold>\<circle>\<^sub>2a/0\<rangle>\<^sub>F p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>F p\<close> by blast
      then show \<open>\<not> \<lbrakk>S\<rbrakk> \<Turnstile> (\<^bold>\<forall>\<^sub>F p)\<close>
        by (auto simp: hdom\<^sub>F_def)
    qed
  qed
qed

end

theorem model_existence:
  fixes S :: \<open>'x fm set\<close>
  assumes \<open>P.prop\<^sub>E Kinds C\<close>
    and \<open>S \<in> C\<close>
    and \<open>P.enough_new S\<close>
    and \<open>p \<in> S\<close>
  shows \<open>\<lbrakk>mk_mcs C S\<rbrakk> \<Turnstile> p\<close>
proof -
  have *: \<open>MyHintikka (mk_mcs C S)\<close>
  proof
    show \<open>P.prop\<^sub>H Kinds (mk_mcs C S)\<close>
      using mk_mcs_Hintikka[OF assms(1-3)] Hintikka.hintikka by blast
  qed
  moreover have \<open>p \<in> mk_mcs C S\<close>
    using assms(4) Extend_subset by blast
  ultimately show ?thesis
    using MyHintikka.model by blast
qed


section \<open>Propositional Semantics\<close>

primrec boolean where
  \<open>boolean _ _ \<^bold>\<bottom> = False\<close>
| \<open>boolean G _ (\<^bold>\<cdot>P ts) = G P ts\<close>
| \<open>boolean G A (p \<^bold>\<longrightarrow> q) = (boolean G A p \<longrightarrow> boolean G A q)\<close>
| \<open>boolean _ A (\<^bold>\<forall>p) = A (\<^bold>\<forall>p)\<close>
| \<open>boolean _ A (\<^bold>\<forall>\<^sub>Pp) = A (\<^bold>\<forall>\<^sub>Pp)\<close>
| \<open>boolean _ A (\<^bold>\<forall>\<^sub>Fp) = A (\<^bold>\<forall>\<^sub>Fp)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>G A. boolean G A p\<close>

proposition \<open>tautology (\<^bold>\<forall>(\<^bold>\<cdot>P [\<^bold>#0]) \<^bold>\<longrightarrow> \<^bold>\<forall>(\<^bold>\<cdot>P [\<^bold>#0]))\<close>
  by simp

lemma boolean_semantics: \<open>boolean (\<lambda>a. \<lblot>E\<^sub>P,G\<rblot>\<^sub>2 a \<circ> map \<lblot>E, E\<^sub>F, C, F\<rblot>) (\<lambda>p. (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p) = (\<lambda>p. (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p)\<close>
proof
  fix p
  show \<open>boolean (\<lambda>a. \<lblot>E\<^sub>P, G\<rblot>\<^sub>2 a \<circ> map \<lblot>E,E\<^sub>F, C, F\<rblot>) ((\<Turnstile>) (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS)) p = ((E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p)\<close>
    by (induct p) simp_all
qed

lemma tautology[simp]: \<open>tautology p \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  using boolean_semantics by metis

proposition \<open>\<exists>p. (\<forall>E E\<^sub>F E\<^sub>P C F G PS FS. (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p) \<and> \<not> tautology p\<close>
  by (metis boolean.simps(4) fun_upd_same semantics_fm.simps(3) semantics_fm.simps(4) tautology)


section \<open>Calculus\<close>

text \<open>Adapted from System Q1 by Smullyan in First-Order Logic (1968).\<close>

inductive Axiomatic (\<open>\<turnstile> _\<close> [50] 50) where
  TA: \<open>tautology p \<Longrightarrow> \<turnstile> p\<close>
| IA: \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t/0\<rangle>p\<close> 
| IA\<^sub>P: \<open>\<turnstile> \<^bold>\<forall>\<^sub>Pp \<^bold>\<longrightarrow> \<langle>s/0\<rangle>\<^sub>Pp\<close> 
| IA\<^sub>F: \<open>\<turnstile> \<^bold>\<forall>\<^sub>Fp \<^bold>\<longrightarrow> \<langle>s/0\<rangle>\<^sub>Fp\<close> 
| MP: \<open>\<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> q\<close> 
| GR: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close> 
| GR\<^sub>P: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>Pp \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Pp\<close>
| GR\<^sub>F: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>Fp \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Fp\<close>

text \<open>We simulate assumptions on the lhs of \<open>\<turnstile>\<close> with a chain of implications on the rhs.\<close>

primrec imply (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto> q) = (p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>

abbreviation Axiomatic_assms (\<open>_ \<turnstile> _\<close> [50, 50] 50) where
  \<open>ps \<turnstile> q \<equiv> \<turnstile> ps \<^bold>\<leadsto> q\<close>

section \<open>Soundness\<close>

fun wf_model where
  \<open>wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<longleftrightarrow> range G \<subseteq> PS \<and> range E\<^sub>P \<subseteq> PS \<and> range F \<subseteq> FS \<and> range E\<^sub>F \<subseteq> FS\<close>

theorem soundness:
  shows \<open>\<turnstile> p \<Longrightarrow> wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
proof (induct p arbitrary: C F G PS FS rule: Axiomatic.induct)
  case (TA p)
  then show ?case
    by simp 
next
  case (IA p t)
  then show ?case
    by auto
next
  case (IA\<^sub>P p s)
  then show ?case
    by (cases s) (fastforce intro!: rangeI)+
next
  case (IA\<^sub>F p s)
  then show ?case
    by (cases s) (fastforce intro!: rangeI)+
next
  case (MP p q)
  then show ?case
    by auto
next
  case (GR q a p)
  moreover from this have \<open>(E, E\<^sub>F, E\<^sub>P, C(a := x), F, G, PS, FS) \<Turnstile> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p)\<close> for x
    unfolding wf_model.simps by meson
  ultimately show ?case
    by fastforce
next
  case (GR\<^sub>P q a p)
  moreover from this have \<open>\<forall>x. x \<in> PS \<longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G(a := x), PS,FS) \<Turnstile> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2a/0\<rangle>\<^sub>Pp)\<close>
    unfolding wf_model.simps
    by (metis (no_types, opaque_lifting) fun_upd_other fun_upd_same image_subset_iff)
  ultimately show ?case
    by fastforce
next
  case (GR\<^sub>F q a p)
  moreover from this have \<open>\<forall>x. x \<in> FS \<longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F(a := x), G, PS,FS) \<Turnstile> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2a/0\<rangle>\<^sub>Fp)\<close>
    unfolding wf_model.simps
    by (metis (no_types, opaque_lifting) fun_upd_other fun_upd_same image_subset_iff)
  ultimately show ?case
    by fastforce
qed

corollary \<open>\<not> (\<turnstile> \<^bold>\<bottom>)\<close>
  using soundness[where p="\<^bold>\<bottom>" and G="\<lambda>p cs. True" and PS="{\<lambda>cs. True}" and E\<^sub>P="\<lambda>n cs. True" and F="\<lambda>p cs. ()"] by fastforce

section \<open>Derived Rules\<close>

lemma Imp1: \<open>\<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  and Imp2: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  and Neg: \<open>\<turnstile> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> p\<close>
  by (auto intro: TA)

text \<open>The tautology axiom TA is not used directly beyond this point.\<close>

lemma Tran': \<open>\<turnstile> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Imp1 Imp2 MP)

lemma Swap: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Imp1 Imp2 Tran' MP)

lemma Tran: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Swap Tran' MP)

text \<open>Note that contraposition in the other direction is an instance of the lemma Tran.\<close>

lemma contraposition: \<open>\<turnstile> (\<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> p) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  by (meson Neg Swap Tran MP)

lemma GR': \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> q \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> q\<close> and a: \<open>a \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>
    using a by (auto intro: GR)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma GR\<^sub>P': \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>\<^sub>Pp \<^bold>\<longrightarrow> q \<Longrightarrow> P \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>\<^sub>Pp \<^bold>\<longrightarrow> q\<close> and a: \<open>P \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>\<^sub>Pp\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>\<^sub>Pp\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Pp\<close>
    using a by (auto intro: GR\<^sub>P)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma GR\<^sub>F': \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>\<^sub>Fp \<^bold>\<longrightarrow> q \<Longrightarrow> F \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>\<^sub>Fp \<^bold>\<longrightarrow> q\<close> and a: \<open>F \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>\<^sub>Fp\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>\<^sub>Fp\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Fp\<close>
    using a by (auto intro: GR\<^sub>F)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma imply_ImpE: \<open>\<turnstile> ps \<^bold>\<leadsto> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (metis Imp1 Swap MP imply.simps(1))
next
  case (Cons r ps)
  have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
    by (meson Cons.hyps Imp1 Imp2 MP)
  then have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
    by (meson Imp1 Imp2 MP)
  then show ?case
    by simp
qed

lemma MP': \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> ps \<turnstile> p \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_ImpE MP by metis

lemma imply_Cons [intro]: \<open>ps \<turnstile> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (auto intro: MP Imp1)

lemma imply_head [intro]: \<open>p # ps \<turnstile> p\<close>
  by (induct ps) (metis Imp1 Imp2 MP imply.simps, metis Imp1 Imp2 MP imply.simps(2))

lemma add_imply [simp]: \<open>\<turnstile> q \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_head by (metis MP imply.simps(2))

lemma imply_mem [simp]: \<open>p \<in> set ps \<Longrightarrow> ps \<turnstile> p\<close>
  using imply_head imply_Cons by (induct ps) fastforce+

lemma deduct1: \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (meson MP' imply_Cons imply_head)

lemma imply_append [iff]: \<open>(ps @ qs \<^bold>\<leadsto> r) = (ps \<^bold>\<leadsto> qs \<^bold>\<leadsto> r)\<close>
  by (induct ps) simp_all

lemma imply_swap_append: \<open>ps @ qs \<turnstile> r \<Longrightarrow> qs @ ps \<turnstile> r\<close>
proof (induct qs arbitrary: ps)
  case Cons
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma deduct2: \<open>p # ps \<turnstile> q \<Longrightarrow> ps \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps imply_append imply_swap_append)

lemmas deduct [iff] = deduct1 deduct2

lemma cut: \<open>p # ps \<turnstile> r \<Longrightarrow> q # ps \<turnstile> p \<Longrightarrow> q # ps \<turnstile> r\<close>
  by (meson MP' deduct(2) imply_Cons)

lemma Boole: \<open>(\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom> \<Longrightarrow> ps \<turnstile> p\<close>
  by (meson MP' Neg add_imply deduct(2))

lemma imply_weaken: \<open>ps \<turnstile> q \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> ps' \<turnstile> q\<close>
  by (induct ps arbitrary: q) (simp, metis MP' deduct(2) imply_mem insert_subset list.simps(15))


section \<open>Derivational Consistency\<close>

interpretation DC: Weak_Derivational_Confl map_fm params_fm \<open>\<lambda>_. True\<close> confl_class \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A ps qs and q :: \<open>'x fm\<close>
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> set A\<close>
  then show \<open>\<not> \<not> A \<turnstile> \<^bold>\<bottom>\<close>
    by cases (simp, metis MP' empty_set equals0D imply_head imply_mem imply_weaken set_ConsD)
qed

interpretation DA: Weak_Derivational_Alpha map_fm params_fm \<open>\<lambda>_. True\<close> alpha_class \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof (standard; safe)
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>\<not> A \<turnstile> \<^bold>\<bottom>\<close> \<open>qs @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CImpN p q)
    then have \<open>A \<turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using *(1) by simp
    moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
      using CImpN(2) * Boole[of q]
      by (metis deduct2 imply.simps(1) imply.simps(2) imply_append)
    ultimately show ?thesis
      using MP' * by blast
  qed
qed

interpretation DB: Weak_Derivational_Beta map_fm params_fm \<open>\<lambda>_. True\<close> beta_class \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>\<not> A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>\<exists>q \<in> set qs. \<not> q # A \<turnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpP p q)
    then show ?thesis
      using * Boole[of p A]
      by (metis MP' deduct2 imply_head imply_weaken insertI2 list.set_intros(1) list.simps(15))
  qed
qed

interpretation DG: Weak_Derivational_Gamma map_tm map_fm params_fm \<open>\<lambda>_. True\<close> G.classify_UNIV \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof (unfold_locales; safe)
  fix A qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma> qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>\<not> A \<turnstile> \<^bold>\<bottom>\<close> \<open>qs t @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CAllP p)
    then show ?thesis
      using * IA[of p t] MP'
      by (metis (mono_tags, lifting) imply.simps(1-2) imply_append imply_swap_append imply_weaken)
  qed
qed

interpretation DG\<^sub>P: Weak_Derivational_Gamma map_sym map_fm params_fm \<open>\<lambda>_. True\<close> G\<^sub>P.classify_UNIV \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof (unfold_locales; safe)
  fix A qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>P qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>\<not> A \<turnstile> \<^bold>\<bottom>\<close> \<open>qs t @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CAllPP p)
    then show ?thesis
      using * IA\<^sub>P[of p t] MP'
      by (metis (mono_tags, lifting) imply.simps(1-2) imply_append imply_swap_append imply_weaken)
  qed
qed

interpretation DG\<^sub>F: Weak_Derivational_Gamma map_sym map_fm params_fm \<open>\<lambda>_. True\<close> G\<^sub>F.classify_UNIV \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof (unfold_locales; safe)
  fix A qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>F qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>\<not> A \<turnstile> \<^bold>\<bottom>\<close> \<open>qs t @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CAllFP p)
    then show ?thesis
      using * IA\<^sub>F[of p t] MP'
      by (metis (mono_tags, lifting) imply.simps(1-2) imply_append imply_swap_append imply_weaken)
  qed
qed

lemma imply_params_fm: \<open>params_fm (ps \<^bold>\<leadsto> q) = params_fm q \<union> (\<Union>p \<in> set ps. params_fm p)\<close>
  by (induct ps) auto

interpretation DD: Weak_Derivational_Delta map_fm params_fm \<open>\<lambda>_. True\<close> \<delta> \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof (standard; safe)
  fix A a and p :: \<open>'x fm\<close>
  assume \<open>p \<in> set A\<close> \<open>a \<notin> P.params (set A)\<close> \<open>\<not> A \<turnstile> \<^bold>\<bottom>\<close> \<open>\<delta> p a @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show False
  proof (induct p a rule: \<delta>.induct)
    case (1 p x)
    have \<open>x \<notin> P.params {p, A \<^bold>\<leadsto> \<^bold>\<bottom>}\<close>
      using 1(1-2) imply_params_fm[of A \<open>\<^bold>\<bottom>\<close>] by auto
    moreover have \<open>\<^bold>\<not> \<langle>\<^bold>\<star>x/0\<rangle>p # A \<turnstile> \<^bold>\<bottom>\<close>
      using 1(4) by simp
    ultimately have \<open>\<^bold>\<not> \<^bold>\<forall>p # A \<turnstile> \<^bold>\<bottom>\<close>
      using GR'[of x p] by simp
    then show ?thesis
      using 1 by (meson Boole MP' imply_mem)
  next
    case (2 p x)
    have \<open>x \<notin> P.params {p, A \<^bold>\<leadsto> \<^bold>\<bottom>}\<close>
      using 2(1-2) imply_params_fm[of A \<open>\<^bold>\<bottom>\<close>] by auto
    moreover have \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>\<^sub>P p # A \<turnstile> \<^bold>\<bottom>\<close>
      using 2(4) by simp
    ultimately have \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>P p # A \<turnstile> \<^bold>\<bottom>\<close>
      using GR\<^sub>P'[of x p] by simp
    then show ?thesis
      using 2 by (meson Boole MP' imply_mem)
  next
    case (3 p x)
    have \<open>x \<notin> P.params {p, A \<^bold>\<leadsto> \<^bold>\<bottom>}\<close>
      using 3(1-2) imply_params_fm[of A \<open>\<^bold>\<bottom>\<close>] by auto
    moreover have \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>\<^sub>F p # A \<turnstile> \<^bold>\<bottom>\<close>
      using 3(4) by simp
    ultimately have \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>F p # A \<turnstile> \<^bold>\<bottom>\<close>
      using GR\<^sub>F'[of x p] by simp
    then show ?thesis
      using 3 by (meson Boole MP' imply_mem)
  qed simp_all
qed

term P.params

interpretation Weak_Derivational_Consistency map_fm params_fm \<open>\<lambda>_. True\<close> Kinds \<open>\<lambda>A. \<not> A \<turnstile> \<^bold>\<bottom>\<close>
proof
  assume \<open>infinite (UNIV :: 'x set)\<close>
  then have inf: \<open>infinite (Collect (\<lambda>_. True) :: 'x set)\<close>
    by simp
  then show \<open>P.prop\<^sub>E Kinds {S :: 'x fm set. \<exists>A. set A = S \<and> \<not> A \<turnstile> \<^bold>\<bottom>}\<close>
    using prop\<^sub>E_Kinds[OF DC.kind[OF inf] DA.kind DB.kind DG.kind DG\<^sub>P.kind DG\<^sub>F.kind DD.kind]
    by blast
qed

theorem weak_completeness:
  fixes p :: \<open>'x fm\<close>
  assumes mod: \<open>\<forall>(E :: _ \<Rightarrow> 'x tm) E\<^sub>F E\<^sub>P C F G PS FS. wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<longrightarrow> (\<forall>q \<in> set ps. (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> q) \<longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
    and \<open>P.enough_new (set ps)\<close>
  shows \<open>ps \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<not> ps \<turnstile> p\<close>
  then have *: \<open>\<not> (\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom>\<close>
    using Boole by blast

  let ?S = \<open>set (\<^bold>\<not> p # ps)\<close>
  let ?C = \<open>{S :: 'x fm set. \<exists>A. set A = S \<and> \<not> A \<turnstile> \<^bold>\<bottom>}\<close>
  let ?M = \<open>\<lbrakk>mk_mcs ?C ?S\<rbrakk>\<close>

  have \<open>infinite (UNIV :: 'x set)\<close>
    using assms(2) card_of_ordLeq_infinite finite_subset inf_univ subset_UNIV
    unfolding P.enough_new_def by blast
  then have \<open>P.prop\<^sub>E Kinds ?C\<close>
    using Consistency by blast
  moreover have \<open>?S \<in> ?C\<close>
    using * by blast
  moreover have \<open>P.enough_new ?S\<close>
    using assms(2) P.infinite_params_left unfolding P.enough_new_def
    by (metis Set_Diff_Un UN_Un card_of_diff inf_univ ordLeq_transitive)
  ultimately have *: \<open>\<forall>p \<in> ?S. ?M \<Turnstile> p\<close>
    using model_existence by blast 
  then have \<open>?M \<Turnstile> p\<close>
    using mod unfolding hdom\<^sub>F_def by auto
  then show False
    using * by simp
qed

theorem completeness:
  fixes p :: \<open>'x fm\<close>
  assumes \<open>\<forall>(E :: nat \<Rightarrow> 'x tm) E\<^sub>P E\<^sub>F C F G PS FS.  wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
    and \<open>|UNIV :: 'x fm set| \<le>o  |UNIV :: 'x set|\<close>
  shows \<open>\<turnstile> p\<close>
  using assms weak_completeness[where ps=\<open>[]\<close>, of p] unfolding P.enough_new_def by simp

section \<open>Natural Deduction\<close>

locale Natural_Deduction
begin

inductive ND_Set :: \<open>'x fm set \<Rightarrow> 'x fm \<Rightarrow> bool\<close> (infix \<open>\<tturnstile>\<close> 50) where
  Assm [dest]: \<open>p \<in> A \<Longrightarrow> A \<tturnstile> p\<close>
| FlsE [elim]: \<open>A \<tturnstile> \<^bold>\<bottom> \<Longrightarrow> A \<tturnstile> p\<close>
| ImpI [intro]: \<open>{p} \<union> A \<tturnstile> q \<Longrightarrow> A \<tturnstile> p \<^bold>\<longrightarrow> q\<close>
| ImpE [dest]: \<open>A \<tturnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<tturnstile> p \<Longrightarrow> A \<tturnstile> q\<close>
| UniI [intro]: \<open>A \<tturnstile> \<langle>\<^bold>\<star>a/0\<rangle>p \<Longrightarrow> a \<notin> P.params ({p} \<union> A) \<Longrightarrow> A \<tturnstile> \<^bold>\<forall>p\<close>
| UniE [dest]: \<open>A \<tturnstile> \<^bold>\<forall>p \<Longrightarrow> A \<tturnstile> \<langle>t/0\<rangle>p\<close>
| UniI\<^sub>P [intro]: \<open>A \<tturnstile> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>P p \<Longrightarrow> a \<notin> P.params ({p} \<union> A) \<Longrightarrow> A \<tturnstile> \<^bold>\<forall>\<^sub>P p\<close>
| UniE\<^sub>P [dest]: \<open>A \<tturnstile> \<^bold>\<forall>\<^sub>P p \<Longrightarrow> A \<tturnstile> \<langle>s/0\<rangle>\<^sub>P p\<close>
| UniI\<^sub>F [intro]: \<open>A \<tturnstile> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>F p \<Longrightarrow> a \<notin> P.params ({p} \<union> A) \<Longrightarrow> A \<tturnstile> \<^bold>\<forall>\<^sub>F p\<close>
| UniE\<^sub>F [dest]: \<open>A \<tturnstile> \<^bold>\<forall>\<^sub>F p \<Longrightarrow> A \<tturnstile> \<langle>s/0\<rangle>\<^sub>F p\<close>
| Clas: \<open>{p \<^bold>\<longrightarrow> q} \<union> A \<tturnstile> p \<Longrightarrow> A \<tturnstile> p\<close>

subsection \<open>Soundness\<close>

theorem soundness_set:
  assumes \<open>A \<tturnstile> p\<close> \<open>wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS)\<close>
  shows \<open>\<forall>q \<in> A. (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> q \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
  using assms
proof (induct A p arbitrary: C F G pred: ND_Set)
  case (UniI A a p)
  have \<open>\<forall>q \<in> A. (E, E\<^sub>F, E\<^sub>P, C(a := x), F, G, PS, FS) \<Turnstile> q\<close> for x
    using UniI(3-) by simp
  moreover have \<open>wf_model (E, E\<^sub>F, E\<^sub>P, C(a := x), F, G, PS, FS)\<close> for x
    using UniI(5) by simp
  ultimately have \<open>(E, E\<^sub>F, E\<^sub>P, C(a := x), F, G, PS, FS) \<Turnstile> \<langle>\<^bold>\<star>a/0\<rangle>p\<close> for x
    using UniI by meson
  then show ?case
    using UniI by simp
next
  case (UniI\<^sub>P A a p)
  have \<open>\<forall>x \<in> PS. \<forall>q \<in> A. (E, E\<^sub>F, E\<^sub>P, C, F, G(a := x), PS, FS) \<Turnstile> q\<close>
    using UniI\<^sub>P(3-) by simp
  moreover have \<open>\<forall>x \<in> PS. wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G(a := x), PS, FS)\<close>
    using UniI\<^sub>P(5) by auto
  ultimately have \<open>\<forall>x \<in> PS. (E, E\<^sub>F, E\<^sub>P, C, F, G(a := x), PS, FS) \<Turnstile> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>P p\<close>
    using UniI\<^sub>P by meson
  then show ?case
    using UniI\<^sub>P by simp
next
  case (UniE\<^sub>P A p s)
  then show ?case
    by (cases s) (fastforce intro!: rangeI)+
next
  case (UniI\<^sub>F A a p)
  have \<open>\<forall>x \<in> FS. \<forall>q \<in> A. (E, E\<^sub>F, E\<^sub>P, C, F(a := x), G, PS, FS) \<Turnstile> q\<close>
    using UniI\<^sub>F(3-) by simp
  moreover have \<open>\<forall>x \<in> FS. wf_model (E, E\<^sub>F, E\<^sub>P, C, F(a := x), G, PS, FS)\<close>
    using UniI\<^sub>F(5) by auto
  ultimately have \<open>\<forall>x \<in> FS. (E, E\<^sub>F, E\<^sub>P, C, F(a := x), G, PS, FS) \<Turnstile> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>\<^sub>F p\<close>
    using UniI\<^sub>F by meson
  then show ?case
    using UniI\<^sub>F by simp
next
  case (UniE\<^sub>F A p s)
  then show ?case
    by (cases s) (fastforce intro!: rangeI)+
qed auto

subsection \<open>Derivational Consistency\<close>

lemma Boole: \<open>{\<^bold>\<not> p} \<union> A \<tturnstile> \<^bold>\<bottom> \<Longrightarrow> A \<tturnstile> p\<close>
  using Clas FlsE by blast

sublocale DC: Derivational_Confl map_fm params_fm \<open>\<lambda>_. True\<close> confl_class \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A ps qs and q :: \<open>'x fm\<close>
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> A\<close>
  then show \<open>\<not> \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
    by cases auto
qed

sublocale DA: Derivational_Alpha map_fm params_fm \<open>\<lambda>_. True\<close> alpha_class \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof (standard; safe)
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<not> A \<tturnstile> \<^bold>\<bottom>\<close> \<open>set qs \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CImpN p q)
    then have \<open>A \<tturnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using *(1) by auto
    moreover have \<open>A \<tturnstile> p \<^bold>\<longrightarrow> q\<close>
      using CImpN(2) * Boole[of q \<open>{p} \<union> A\<close>] by auto
    ultimately show ?thesis
      using * by blast
  qed
qed

sublocale DB: Derivational_Beta map_fm params_fm \<open>\<lambda>_. True\<close> beta_class \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<not> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>\<exists>q \<in> set qs. \<not> {q} \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpP p q)
    then show ?thesis
      using * Boole[of p A]
      by (metis Assm ImpE ImpI list.set_intros(1) set_subset_Cons subset_iff)
  qed
qed

sublocale DG: Derivational_Gamma map_tm map_fm params_fm \<open>\<lambda>_. True\<close> G.classify_UNIV \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof (unfold_locales; safe)
  fix A qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<not> A \<tturnstile> \<^bold>\<bottom>\<close> \<open>set (qs t) \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CAllP p)
    then show ?thesis
      using * UniE[of A p t] ImpI by auto
  qed
qed

sublocale DGP: Derivational_Gamma map_sym map_fm params_fm \<open>\<lambda>_. True\<close> G\<^sub>P.classify_UNIV \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof (unfold_locales; safe)
  fix A qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>P qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<not> A \<tturnstile> \<^bold>\<bottom>\<close> \<open>set (qs t) \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CAllPP p)
    then show ?thesis
      using * UniE\<^sub>P[of A p t] ImpI by auto
  qed
qed

sublocale DGF: Derivational_Gamma map_sym map_fm params_fm \<open>\<lambda>_. True\<close> G\<^sub>F.classify_UNIV \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof (unfold_locales; safe)
  fix A qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>F qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<not> A \<tturnstile> \<^bold>\<bottom>\<close> \<open>set (qs t) \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show False
  proof cases
    case (CAllFP p)
    then show ?thesis
      using * UniE\<^sub>F[of A p t] ImpI by auto
  qed
qed

sublocale DD: Derivational_Delta map_fm params_fm \<open>\<lambda>_. True\<close> \<delta> \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
proof (standard; safe)
  fix A a and p :: \<open>'x fm\<close>
  assume \<open>p \<in> A\<close> \<open>a \<notin> P.params A\<close> \<open>\<not> A \<tturnstile> \<^bold>\<bottom>\<close>  \<open>set (\<delta> p a) \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show False
  proof (induct p a rule: \<delta>.induct)
    case (1 p x)
    then have \<open>x \<notin> P.params ({p} \<union> A)\<close>
      by auto
    moreover have \<open>A \<tturnstile> \<langle>\<^bold>\<star>x/0\<rangle> p\<close>
      using 1(4) Boole by auto
    ultimately show ?case
      using 1 UniI by blast
  next
    case (2 p x)
    then have \<open>x \<notin> P.params ({p} \<union> A)\<close>
      by auto
    moreover have \<open>A \<tturnstile> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>\<^sub>P p\<close>
      using 2(4) Boole by auto
    ultimately show ?case
      using 2 UniI\<^sub>P by blast
  next
    case (3 p x)
    then have \<open>x \<notin> P.params ({p} \<union> A)\<close>
      by auto
    moreover have \<open>A \<tturnstile> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>\<^sub>F p\<close>
      using 3(4) Boole by auto
    ultimately show ?case
      using 3 UniI\<^sub>F by blast
  qed simp_all
qed

sublocale Derivational_Consistency map_fm params_fm \<open>\<lambda>_. True\<close> Kinds \<open>\<lambda>A. \<not> A \<tturnstile> \<^bold>\<bottom>\<close>
  using prop\<^sub>E_Kinds[OF DC.kind DA.kind DB.kind DG.kind DGP.kind DGF.kind DD.kind] by unfold_locales

subsection \<open>Strong Completeness\<close>

theorem strong_completeness:
  fixes p :: \<open>'x fm\<close>
  assumes mod: \<open>\<And>(E :: nat \<Rightarrow> 'x tm) E\<^sub>F E\<^sub>P C F G PS FS. wf_model (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Longrightarrow>
      (\<forall>q \<in> A. (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> q) \<Longrightarrow> (E, E\<^sub>F, E\<^sub>P, C, F, G, PS, FS) \<Turnstile> p\<close>
    and \<open>P.enough_new A\<close>
  shows \<open>A \<tturnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<not> A \<tturnstile> p\<close>
  then have *: \<open>\<not> {\<^bold>\<not> p} \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
    using Boole by (metis insert_is_Un)

  let ?S = \<open>set [\<^bold>\<not> p] \<union> A\<close>
  let ?C = \<open>{A. P.enough_new A \<and> \<not> A \<tturnstile> \<^bold>\<bottom>}\<close>
  let ?M = \<open>\<lbrakk>mk_mcs ?C ?S\<rbrakk>\<close>

  have wf: \<open>wf_model ?M\<close>
    unfolding hdom\<^sub>F_def by simp

  have \<open>P.prop\<^sub>E Kinds ?C\<close>
    using Consistency by blast
  moreover have \<open>P.enough_new ?S\<close>
    using assms(2) params_left by blast
  moreover from this have \<open>?S \<in> ?C\<close>
    using * by simp
  ultimately have *: \<open>\<forall>p \<in> ?S. ?M \<Turnstile> p\<close>
    using model_existence by blast
  then have \<open>?M \<Turnstile> p\<close>
    using mod[OF wf] by fast 
  then show False
    using * by simp
qed

proposition \<open>\<exists>M. wf_model M\<close>
  by (meson sup.cobounded2 sup_ge1 wf_model.simps)

end

end

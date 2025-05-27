theory Ground_Context
  imports Ground_Term_Extra
begin

type_synonym 'f ground_context = "('f, 'f gterm) actxt"

abbreviation (input) GHole (\<open>\<box>\<^sub>G\<close>) where
  "\<box>\<^sub>G \<equiv> Hole"

abbreviation ctxt_apply_gterm (\<open>_\<langle>_\<rangle>\<^sub>G\<close> [1000, 0] 1000) where
  "C\<langle>s\<rangle>\<^sub>G \<equiv> GFun\<langle>C;s\<rangle>"

lemma le_size_gctxt: "size t \<le> size (c\<langle>t\<rangle>\<^sub>G)"
  by (induction c) simp_all

lemma lt_size_gctxt: "c \<noteq> \<box>\<^sub>G \<Longrightarrow> size t < size c\<langle>t\<rangle>\<^sub>G"
  by (induction c) force+

lemma gctxt_ident_iff_eq_GHole[simp]: "c\<langle>t\<rangle>\<^sub>G = t \<longleftrightarrow> c = \<box>\<^sub>G"
proof (rule iffI)
  assume "c\<langle>t\<rangle>\<^sub>G = t"

  hence "size (c\<langle>t\<rangle>\<^sub>G) = size t"
    by argo

  thus "c = \<box>\<^sub>G"
    using lt_size_gctxt[of c t]
    by linarith
next
  show "c = \<box>\<^sub>G \<Longrightarrow> c\<langle>t\<rangle>\<^sub>G = t"
    by simp
qed

end

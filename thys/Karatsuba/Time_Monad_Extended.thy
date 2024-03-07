theory Time_Monad_Extended
  imports Root_Balanced_Tree.Time_Monad
begin

section "Some Automation for @{theory Root_Balanced_Tree.Time_Monad}"

text "A bit of automation for statements involving the @{const time} component."

lemma time_bind_tm: "time (s \<bind> f) = time s + time (f (val s))"
  unfolding bind_tm_def
  by (simp split: tm.splits)

lemma time_tick: "time (tick s) = 1"
  by (simp add: tick_def)

lemmas tm_time_simps[simp] = time_bind_tm time_return time_tick if_distrib[of time]

lemma bind_tm_cong[fundef_cong]:
  assumes "f1 = f2"
  assumes "g1 (val f1) = g2 (val f2)"
  shows "f1 \<bind> g1 = f2 \<bind> g2"
  using assms unfolding bind_tm_def
  by (auto split: tm.splits)

text "Introduce @{text val_simp} as named theorem. The idea is to collect simplification rules for
the @{const val} component that can be unfolded on their own."

named_theorems val_simp
declare val_simps[val_simp]

end
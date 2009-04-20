header {* \isachapter{The Framework} 
  \isaheader{Basic Definitions} *}

theory BasicDefs imports Aux begin

subsection{* Edge kinds *}

datatype 'state edge_kind = Update "'state \<Rightarrow> 'state"           ("\<Up>_")
                          | Predicate "'state \<Rightarrow> bool"      ("'(_')\<^isub>\<surd>")


subsection {* Transfer and predicate functions *}

fun transfer :: "'state edge_kind \<Rightarrow> 'state \<Rightarrow> 'state"
where "transfer (\<Up>f) s = f s"
  | "transfer (P)\<^isub>\<surd> s   = s"

fun transfers :: "'state edge_kind list \<Rightarrow> 'state \<Rightarrow> 'state"
where "transfers [] s   = s"
  | "transfers (e#es) s = transfers es (transfer e s)"

fun pred :: "'state edge_kind \<Rightarrow> 'state \<Rightarrow> bool"
where "pred (\<Up>f) s = True"
  | "pred (P)\<^isub>\<surd> s   = (P s)"

fun preds :: "'state edge_kind list \<Rightarrow> 'state \<Rightarrow> bool"
where "preds [] s   = True"
  | "preds (e#es) s = (pred e s \<and> preds es (transfer e s))"



lemma transfers_split:
  "(transfers (ets@ets') s) = (transfers ets' (transfers ets s))"
by(induct ets arbitrary:s) auto

lemma preds_split:
  "(preds (ets@ets') s) = (preds ets s \<and> preds ets' (transfers ets s))"
by(induct ets arbitrary:s) auto


lemma transfers_id_no_influence:
  "transfers [et \<leftarrow> ets. et \<noteq> \<Up>id] s = transfers ets s"
by(induct ets arbitrary:s,auto)

lemma preds_True_no_influence:
  "preds [et \<leftarrow> ets. et \<noteq> (\<lambda>s. True)\<^isub>\<surd>] s = preds ets s"
by(induct ets arbitrary:s,auto)

end

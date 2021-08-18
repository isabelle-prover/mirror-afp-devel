theory Automation_Setup
imports "System_Specification"
begin

lemma add_prop:
  assumes "PROP (T)"
  shows "A ==> PROP (T)"
  using assms .

lemmas exhaust_elim =
   cAct.exhaust[of x, THEN add_prop[where A="a=Cact x"], rotated -1]
   uAct.exhaust[of x, THEN add_prop[where A="a=Uact x"], rotated -1]
   uuAct.exhaust[of x, THEN add_prop[where A="a=UUact x"], rotated -1]
   rAct.exhaust[of x, THEN add_prop[where A="a=Ract x"], rotated -1]
   lAct.exhaust[of x, THEN add_prop[where A="a=Lact x"], rotated -1]
  for x a

lemma Paper_dest_conv:
  "(p =
        Paper title abstract content reviews dis decs) \<longleftrightarrow>
  title = titlePaper p \<and>
  abstract = abstractPaper p \<and>
  content = contentPaper p \<and>
  reviews = reviewsPaper p \<and>
  dis = disPaper p \<and>
  decs = decsPaper p
  "
  by (cases p) auto

end

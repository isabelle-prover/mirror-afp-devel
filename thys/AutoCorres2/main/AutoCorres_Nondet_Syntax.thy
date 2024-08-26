theory AutoCorres_Nondet_Syntax
imports AutoCorres2.AutoCorres
begin

section \<open>Hide legacy nondet monad from user\<close>


hide_const L2Defs.gets_theE




no_notation L1Valid.validE ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)")
hide_const L1Valid.validE


definition gets_theE ::
    "('s \<Rightarrow> 'b option) \<Rightarrow> ('e, 'b, 's) exn_monad" where 
    "gets_theE \<equiv> \<lambda>x. (liftE (gets_the x))"

section \<open>Legacy syntax layer to mimic the nondet monad\<close>

abbreviation (input) bindE:: 
  "('e,'a,'s) exn_monad \<Rightarrow> ('a \<Rightarrow> ('e, 'b, 's) exn_monad) \<Rightarrow> ('e, 'b, 's) exn_monad"  (infixl ">>=E" 60) where 
  "bindE \<equiv> bind"

abbreviation (input) bind_nd:: 
  "('a,'s) res_monad \<Rightarrow> ('a \<Rightarrow> ('b, 's) res_monad) \<Rightarrow> ('b, 's) res_monad" where 
  "bind_nd \<equiv> bind"

abbreviation (input) throwError::"'e \<Rightarrow> ('e, 'a, 's) exn_monad" where 
  "throwError \<equiv> throw"

abbreviation (input) guardE:: "('s \<Rightarrow> bool) \<Rightarrow> ('e, unit, 's) exn_monad" where 
  "guardE \<equiv> guard"

abbreviation (input) returnOk:: "'a \<Rightarrow> ('e, 'a, 's) exn_monad" where 
  "returnOk \<equiv> return"
 
abbreviation (input) whenE:: "bool \<Rightarrow> ('e, unit, 's) exn_monad \<Rightarrow> ('e, unit, 's) exn_monad" where
  "whenE \<equiv> when"

abbreviation (input) unlessE:: "bool \<Rightarrow> ('e, unit, 's) exn_monad \<Rightarrow> ('e, unit, 's) exn_monad" where
  "unlessE \<equiv> unless"

abbreviation (input) modifyE:: "('s \<Rightarrow> 's) \<Rightarrow> ('e, unit, 's) exn_monad" where
  "modifyE \<equiv> modify"

abbreviation (input) selectE:: "'a set \<Rightarrow> ('e, 'a, 's) exn_monad" where
  "selectE \<equiv> select"

abbreviation (input) unknownE:: "('e, 'a, 's) exn_monad" where
  "unknownE \<equiv> unknown"

abbreviation (input) getsE:: "('s \<Rightarrow> 'a) \<Rightarrow> ('e, 'a, 's) exn_monad" where
  "getsE \<equiv> gets"

abbreviation (input) skipE:: "('e, unit, 's) exn_monad" where
  "skipE \<equiv> skip"

abbreviation (input) whileLoopE::
  "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('e, 'a, 's) exn_monad) \<Rightarrow> 'a \<Rightarrow> ('e, 'a, 's) exn_monad"
  where
  "whileLoopE \<equiv> whileLoop"

abbreviation (input) handleE':: 
  "('e, 'a, 's) exn_monad \<Rightarrow> ('e \<Rightarrow> ('f, 'a, 's) exn_monad) \<Rightarrow> ('f, 'a, 's) exn_monad" 
  (infix "<handle2>" 10)
  where
  "handleE' \<equiv> catch"

abbreviation (input) handleE:: 
  "('e, 'a, 's) exn_monad \<Rightarrow> ('e \<Rightarrow> ('e, 'a, 's) exn_monad) \<Rightarrow> ('e, 'a, 's) exn_monad" 
  (infix "<handle>" 10)
  where
  "handleE \<equiv> catch"

nonterminal
  dobinds and dobind and nobind

syntax (input)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ \<leftarrow>/ _)" 10)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ <-/ _)" 10)
  ""           :: "dobind => dobinds"                 ("_")
  "_nobind"    :: "'a => dobind"                      ("_")
  "_dobinds"   :: "[dobind, dobinds] => dobinds"      ("(_);//(_)")

  "_do"        :: "[dobinds, 'a] => 'a"               ("(do ((_);//(_))//od)" 100)
  "_doE" :: "[dobinds, 'a] => 'a"  ("(doE ((_);//(_))//odE)" 100)

translations
  "_do (_dobinds b bs) e"  \<rightharpoonup> "_do b (_do bs e)"
  "_do (_nobind b) e"      \<rightharpoonup> "CONST bind_nd b (\<lambda>_. e)"
  "do x <- a; e od"        \<rightharpoonup> "CONST bind_nd a (\<lambda>x. e)"

  "_doE (_dobinds b bs) e"  \<rightharpoonup> "_doE b (_doE bs e)"
  "_doE (_nobind b) e"      \<rightharpoonup> "CONST bindE b (\<lambda>_. e)"
  "doE x <- a; e odE"       \<rightharpoonup> "CONST bindE a (\<lambda>x. e)"

term "doE x <- f; g x odE"
term "do x <- f; g x od"

syntax
  "_doO" :: "[dobinds, 'a] => 'a"  ("(DO (_);//   (_)//OD)" 100)

translations
  "_doO (_dobinds b bs) e" == "_doO b (_doO bs e)"
  "_doO (_nobind b) e"     == "b |>> (\<lambda>_.  e)"
  "DO x <- a; e OD"        == "a |>> (\<lambda>x. e)"

term "DO x <- ogets (\<lambda>_. 2); oguard (\<lambda>s. b \<noteq> 0); oreturn x OD"

end

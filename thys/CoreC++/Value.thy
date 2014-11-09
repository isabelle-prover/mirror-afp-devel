(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

   Based on the Jinja theory Common/Value.thy by David von Oheimb and Tobias Nipkow 
*)

section {* CoreC++ values *}

theory Value imports Type begin


type_synonym addr = nat
type_synonym path = "cname list"            -- "Path-component in subobjects"
type_synonym reference = "addr \<times> path"

datatype val
  = Unit           -- "dummy result value of void expressions"
  | Null           -- "null reference"
  | Bool bool      -- "Boolean value"
  | Intg int       -- "integer value" 
  | Ref reference  -- "Address on the heap and subobject-path"

primrec the_Intg :: "val \<Rightarrow> int" where
  "the_Intg (Intg i) = i"

primrec the_addr :: "val \<Rightarrow> addr" where
  "the_addr (Ref r) = fst r"

primrec the_path :: "val \<Rightarrow> path" where
  "the_path (Ref r) = snd r"

primrec default_val :: "ty \<Rightarrow> val"   -- "default value for all types" where
  "default_val Void       = Unit"
| "default_val Boolean    = Bool False"
| "default_val Integer    = Intg 0"
| "default_val NT         = Null"
| "default_val (Class C)  = Null"

lemma default_val_no_Ref:"default_val T = Ref(a,Cs) \<Longrightarrow> False"
by(cases T)simp_all

primrec typeof :: "val \<Rightarrow> ty option" where
  "typeof Unit     = Some Void"
| "typeof Null     = Some NT"
| "typeof (Bool b) = Some Boolean"
| "typeof (Intg i) = Some Integer"
| "typeof (Ref r)  = None"

lemma [simp]: "(typeof v = Some Boolean) = (\<exists>b. v = Bool b)"
by(induct v) auto

lemma [simp]: "(typeof v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v) auto

lemma [simp]: "(typeof v = Some NT) = (v = Null)"
 by(cases v) auto

lemma [simp]: "(typeof v = Some Void) = (v = Unit)"
 by(cases v) auto

end

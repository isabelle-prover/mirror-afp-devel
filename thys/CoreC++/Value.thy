(*  Title:       CoreC++
    ID:          $Id: Value.thy,v 1.4 2006-06-28 09:09:19 wasserra Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

   Based on the Jinja theory Common/Value.thy by David von Oheimb and Tobias Nipkow 
*)


header {* CoreC++ values *}

theory Value imports Type begin

types 
  addr = nat
  path = "cname list"            -- "Path-component in subobjects"
  reference = "addr \<times> path"

datatype val
  = Unit           -- "dummy result value of void expressions"
  | Null           -- "null reference"
  | Bool bool      -- "Boolean value"
  | Intg int       -- "integer value" 
  | Ref reference  -- "Address on the heap and subobject-path"

consts
  the_Intg :: "val \<Rightarrow> int"
  the_addr :: "val \<Rightarrow> addr"
  the_path :: "val \<Rightarrow> path"

primrec
  "the_Intg (Intg i) = i"

primrec
  "the_addr (Ref r) = fst r"

primrec
  "the_path (Ref r) = snd r"

consts
  default_val :: "ty \<Rightarrow> val"   -- "default value for all types"

primrec
  "default_val Void       = Unit"
  "default_val Boolean    = Bool False"
  "default_val Integer    = Intg 0"
  "default_val NT         = Null"
  "default_val (Class C)  = Null"

lemma default_val_no_Ref:"default_val T = Ref(a,Cs) \<Longrightarrow> False"
by(cases T)simp_all

consts
  typeof :: "val \<Rightarrow> ty option"
primrec
  "typeof Unit     = Some Void"
  "typeof Null     = Some NT"
  "typeof (Bool b) = Some Boolean"
  "typeof (Intg i) = Some Integer"
  "typeof (Ref r)  = None"

lemma [simp]: "(typeof v = Some Boolean) = (\<exists>b. v = Bool b)"
by(induct v) auto

lemma [simp]: "(typeof v = Some Integer) = (\<exists>i. v = Intg i)"
by(cases v) auto

lemma [simp]: "(typeof v = Some NT) = (v = Null)"
 by(cases v) auto

lemma [simp]: "(typeof v = Some Void) = (v = Unit)"
 by(cases v) auto


end

(*  Title:      Jinja/Common/Value.thy
    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

section {* Jinja Values *}

theory Value imports TypeRel begin

type_synonym addr = nat

datatype val
  = Unit        -- "dummy result value of void expressions"
  | Null        -- "null reference"
  | Bool bool   -- "Boolean value"
  | Intg int    -- "integer value" 
  | Addr addr   -- "addresses of objects in the heap"

primrec the_Intg :: "val \<Rightarrow> int" where
  "the_Intg (Intg i) = i"

primrec the_Addr :: "val \<Rightarrow> addr" where
  "the_Addr (Addr a) = a"

primrec default_val :: "ty \<Rightarrow> val"   -- "default value for all types" where
  "default_val Void      = Unit"
| "default_val Boolean   = Bool False"
| "default_val Integer   = Intg 0"
| "default_val NT        = Null"
| "default_val (Class C) = Null"

end

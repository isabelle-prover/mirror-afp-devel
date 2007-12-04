(*  Title:      JinjaThreads/Common/Value.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Value.thy by David von Oheimb and Tobias Nipkow

*)

header {* \isaheader{Jinja Values} *}

theory Value imports TypeRel begin

types addr = nat

datatype val
  = Unit        -- "dummy result value of void expressions"
  | Null        -- "null reference"
  | Bool bool   -- "Boolean value"
  | Intg int    -- "integer value" 
  | Addr addr   -- "addresses of objects, arrays and threads in the heap"

consts
  the_Intg :: "val \<Rightarrow> int"
  the_Addr :: "val \<Rightarrow> addr"

primrec
  "the_Intg (Intg i) = i"

primrec
  "the_Addr (Addr a) = a"

consts
  default_val :: "ty \<Rightarrow> val"   -- "default value for all types"

primrec
  "default_val Void      = Unit"
  "default_val Boolean   = Bool False"
  "default_val Integer   = Intg 0"
  "default_val NT        = Null"
  "default_val (Class C) = Null"
  "default_val (Array A) = Null"
end

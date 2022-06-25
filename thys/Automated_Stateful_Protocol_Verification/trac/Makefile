#!/bin/sh
# SPDX-License-Identifier: BSD-3-Clause

ISABELLE=isabelle

all: trac_parser/trac_fp.lex.sml trac_parser/trac_fp.grm.sig trac_parser/trac_protocol.lex.sml trac_parser/trac_protocol.grm.sig

test:
	isabelle build -c -D .

clean:
	rm -f trac_parser/*.lex.sml trac_parser/*.grm.sml trac_parser/*.grm.sig

%.lex.sml: %.lex
	bin/ml-lex-isa $< 
%.grm.sig: %.grm
	bin/ml-yacc-isa $< 


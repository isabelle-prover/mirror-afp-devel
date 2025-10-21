# Verified program analysis with Datalog
Collaboration on verified program analysis with Datalog.

Authors: 
Anders Schlichtkrull
René Rydhof Hansen
Flemming Nielson


## Opening the files

If you already have installed Isabelle2025 (https://isabelle.in.tum.de/website-Isabelle2025/) 
and the 2025 version of Archive of Formal Proofs (https://foss.heptapod.net/isa-afp/afp-2025).
AFP is installed with the command
``
isabelle components -u /home/myself/afp/thys
''
and then you can open Isabelle/jEdit and inspect our proofs:
```
cd LTS-formalization/Datalog
isabelle jedit -d .
```

## Download the version considered in our SAC2023 paper

```
$ git clone --branch SAC2023 https://github.com/anderssch/LTS-formalization/
```

The files will then be in `LTS-formalization/Datalog`

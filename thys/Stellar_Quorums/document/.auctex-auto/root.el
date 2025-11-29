;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "root"
 (lambda ()
   (LaTeX-add-bibitems
    "disc_paper"
    "MazieresStellarConsensusProtocol2015"))
 '(or :bibtex :latex))


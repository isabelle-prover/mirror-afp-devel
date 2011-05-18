(TeX-add-style-hook "root"
 (lambda ()
    (LaTeX-add-bibliographies)
    (LaTeX-add-environments
     '("isactab" 1)
     '("isatab" 1))
    (LaTeX-add-labels
     "sec:introduction"
     "sec:robot-example"
     "sec:perspective")
    (TeX-add-symbols
     '("Thmref" 1)
     '("thmref" 1)
     '("Tblref" 1)
     '("tblref" 1)
     '("Figref" 1)
     '("figref" 1)
     '("Secref" 1)
     '("secref" 1)
     '("code" 1)
     '("ColDefs" 1)
     '("Defs" 1)
     '("isahex" 1)
     '("isafun" 1)
     "titl"
     "stitl"
     "atitl"
     "gcalt")
    (TeX-run-style-hooks
     "pdfsetup"
     "color"
     "booktabs"
     "babel"
     "greek"
     "english"
     "amssymb"
     "wrapfig"
     "graphicx"
     "url"
     "isabellesym"
     "isabelle"
     "latex2e"
     "llncs10"
     "llncs"
     "session")))

